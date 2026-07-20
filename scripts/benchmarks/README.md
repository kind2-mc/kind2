# PR benchmark comparison

CI harness that replaces the remote-cluster webhook (`webhook-handler` +
`test_pr`). On every pull request it builds Kind 2 at the PR head **and** at the
base commit and benchmarks each over a fixed set — the two legs run **in
parallel** (a `[head, base]` job matrix); within each leg the benchmark set runs
sequentially. A final `compare` job joins the two stat files and fails the check
if the PR introduces a **regression** or a **soundness bug**.

Driven by [`.github/workflows/kind2-pr-benchmarks.yml`](../../.github/workflows/kind2-pr-benchmarks.yml).

## Scripts

- `run-benchmarks.sh <kind2_bin> <timeout_s> <out_stat> <bench_root> [subdir...]`
  Runs `<kind2_bin>` over every `*.lus` under each `<bench_root>/<subdir>`
  (or all of `<bench_root>` if no subdir is given) sequentially and writes one
  line per benchmark to `<out_stat>`:
  `<relative/path.lus> <Valid|Invalid|Timeout|Error|Mixed> <wall_seconds>`,
  where the path is relative to `<bench_root>`. Uses Kind 2's `--timeout_wall`
  (soft) wrapped in `timeout` (hard kill), and classifies output with the same
  distinguished strings the cluster's `benchmark-stat` used for the `kind-2`
  profile. Extra Kind 2 flags can be passed via `KIND2_EXTRA_ARGS`.

- `compare-benchmarks.sh <head_stat> <base_stat> [summary_file]`
  Joins the two stat files and writes a Markdown report (to
  `$GITHUB_STEP_SUMMARY` in CI). Exit codes:
  - `2` — soundness bug: base `Invalid` → head `Valid`
  - `1` — regression: base `Valid` → head not `Valid`/`Timeout`, or
           base `Invalid` → head not `Invalid`/`Timeout`
  - `0` — no regressions

  A head `Timeout` where the base solved the benchmark is reported for
  information only, not treated as a regression (CI runner timing is noisy).

## Configuration (must be set before enabling)

The benchmark set is checked out from a **separate repository**. Edit the `env`
block in the workflow:

| Variable             | Meaning                                                      |
|----------------------|--------------------------------------------------------------|
| `BENCHMARKS_REPO`    | `owner/repo` holding the benchmark set                       |
| `BENCHMARKS_REF`     | branch/tag/sha to pin                                        |
| `BENCHMARKS_SUBDIRS` | space-separated dirs to run, relative to the repo root       |
| `BENCH_TIMEOUT`      | per-benchmark wall timeout, seconds (default `45`)           |

Currently set to `FMCAD08/Bool FMCAD08/Int FMCAD08/Real_Int` on the `main`
branch of `kind2-mc/kind2-benchmarks`.

If the benchmarks repo is private, uncomment `token:` in the *Checkout
benchmarks* step and add a read-only PAT secret.

## Later optimizations (not done yet)

The PR head and base legs already run in parallel, but each leg runs its
benchmark set sequentially. To speed a leg up, shard its file list across a
sub-matrix (each shard runs a slice of the `*.lus`), then concatenate the shard
stat files before the `compare` job — recovering more of the parallelism the
4-node cluster provided.
