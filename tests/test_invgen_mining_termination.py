"""The invariant generator stops mining when it is asked to terminate.

Before it ever asks a solver, the integer invariant generator mines its
candidate terms, forming octagons out of the pairs of integer terms of the
system, and builds its graphs. It only checked for a termination request
once it started querying. On a system with many integer variables the mining
takes seconds, the property is proved long before it ends, and killing the
generator's solvers does not unblock it: the supervisor waited the whole of
its ten-second deadline before giving up on the generator.

The model is generated: 160 accumulators, and a property over all of them
that 1-induction proves at once. The run must end soon after.
"""

import json
import subprocess
import time

from conftest import common_args, kind2_bin, run_timeout

n = 160

model = "\n".join(
    [
        "node main ("
        + "; ".join(f"x{i}: int" for i in range(n))
        + ") returns (ok: bool);",
        "var " + "; ".join(f"s{i}: int" for i in range(n)) + "; t, u: int;",
        "let",
        *[f"  s{i} = x{i} -> pre s{i} + x{i};" for i in range(n)],
        "  t = " + " + ".join(f"s{i}" for i in range(n)) + ";",
        "  u = " + " + ".join(f"s{i}" for i in reversed(range(n))) + ";",
        "  ok = t = u;",
        "  check ok;",
        "tel",
    ]
)


def test_run_ends_while_invariant_generator_mines(tmp_path):
    path = tmp_path / "many_accumulators.lus"
    path.write_text(model)
    arg_list = [arg for pair in common_args.items() for arg in pair]
    started = time.monotonic()
    proc = subprocess.run(
        [kind2_bin, "-json", *arg_list, str(path)],
        capture_output=True,
        text=True,
        timeout=run_timeout,
    )
    elapsed = time.monotonic() - started
    answers = [
        obj["answer"]["value"]
        for obj in json.loads(proc.stdout)
        if obj.get("objectType") == "property"
    ]
    assert answers == ["valid"], answers
    assert proc.returncode == 0
    # The supervisor gives up on an engine after ten seconds
    assert elapsed < 6, elapsed
