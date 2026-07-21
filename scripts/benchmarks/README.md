# PR benchmark comparison

CI harness that replaces the remote-cluster webhook (`webhook-handler` +
`test_pr`). On every pull request it builds Kind 2 at the PR head **and** at the
base commit and benchmarks each over a fixed set, then fails the check if the PR
introduces a **regression** or a **soundness bug**.

Pipeline (`build` → `benchmark` → `compare`):

1. **`build` (matrix: `side`)** — build Kind 2 at each side once; upload the
   binary as an artifact.
2. **`benchmark` (matrix: `side` × `shard`)** — download the binary and run one
   shard of the benchmark set (round-robin over the sorted file list); upload
   the shard's stat file. All `side × SHARD_COUNT` shards run in parallel.
3. **`compare`** — concatenate the shard stat files per side, join head vs.
   base, write a Markdown Step Summary (result counts per version + regressions,
   soundness bugs, and improvements), and set the check's exit status.

Driven by [`.github/workflows/kind2-pr-benchmarks.yml`](../../.github/workflows/kind2-pr-benchmarks.yml).

## Scripts

- `run-benchmarks.sh <kind2_bin> <timeout_s> <out_stat> <bench_root> [subdir...]`
  Runs `<kind2_bin>` over every `*.lus` under each `<bench_root>/<subdir>`
  (or all of `<bench_root>` if no subdir is given) sequentially and writes one
  line per benchmark to `<out_stat>`:
  `<relative/path.lus> <Valid|Invalid|Timeout|Error|Mixed> <wall_seconds>`,
  where the path is relative to `<bench_root>` (plus a 4th `<shard>` column when
  sharding, so the comparison can name the job whose log holds an errored
  benchmark's output). Uses Kind 2's `--timeout_wall`
  (soft) wrapped in `timeout` (hard kill), and classifies output with the same
  distinguished strings the cluster's `benchmark-stat` used for the `kind-2`
  profile. Extra Kind 2 flags can be passed via `KIND2_EXTRA_ARGS`. Set
  `SHARD_COUNT`/`SHARD_INDEX` (env) to run only one round-robin shard of the set.

- `compare-benchmarks.sh <head_stat> <base_stat> [summary_file]`
  Joins the two stat files and writes a Markdown report (to
  `$GITHUB_STEP_SUMMARY` in CI). Exit codes:
  - `2` — soundness bug: the head flips a property between `Valid` and `Invalid`
          vs. the base, in either direction — base `Invalid` → head `Valid`
          (unsound for verification) or base `Valid` → head `Invalid` (unsound
          for falsification)
  - `1` — regression: base `Valid`/`Invalid` → head `Error` (a solved benchmark
          the PR can no longer solve, other than a noisy `Timeout`)
  - `0` — no regressions or soundness bugs

  A head `Timeout` where the base solved the benchmark is reported for
  information only, not treated as a regression (CI runner timing is noisy).
  The Errors table names the shard job (`benchmark (head <N>)`) whose log
  contains each errored benchmark's Kind 2 output.

## Configuration (must be set before enabling)

The benchmark set is checked out from a **separate repository**. Edit the `env`
block in the workflow:

| Variable             | Meaning                                                      |
|----------------------|--------------------------------------------------------------|
| `BENCHMARKS_REPO`    | `owner/repo` holding the benchmark set                       |
| `BENCHMARKS_REF`     | branch/tag/sha to pin                                        |
| `BENCHMARKS_SUBDIRS` | space-separated dirs to run, relative to the repo root       |
| `BENCH_TIMEOUT`      | per-benchmark wall timeout, seconds (default `45`)           |
| `SHARD_COUNT`        | shards per side; **must** match the `shard` matrix length    |

Currently set to `FMCAD08/Bool FMCAD08/Int FMCAD08/Real_Int` on the `main`
branch of `kind2-mc/kind2-benchmarks`.

To change the shard count, edit **both** `SHARD_COUNT` and the `shard: [...]`
matrix list in the `benchmark` job so their lengths agree.

If the benchmarks repo is private, uncomment `token:` in the *Checkout
benchmarks* step and add a read-only PAT secret.

## Tuning

Wall-clock time is dominated by the slowest shard. Increasing `SHARD_COUNT`
shortens each shard but adds fixed per-job overhead (checkout + Z3 install) and
consumes more concurrent runners. The `Int` subset dominates the set, and the
~60 benchmarks that hit the timeout are spread across shards by the round-robin
split.
