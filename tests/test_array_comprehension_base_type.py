"""The local of an array comprehension has the base type of the comprehension.

The type of a comprehension may have refinement types, such as the subrange
type of the values of its body. The fresh local it is compiled to is declared
with the base type, so that it carries no subtype obligation of its own: only
the variables the comprehension is assigned to do.
"""

import subprocess

from conftest import common_args, kind2_bin, run_timeout

model = """type cval = subrange [0, 9] of int;
const one: cval = 1;
const two: cval = 2;

node N () returns (v: cval^2);
let
  v = (if i = 0 then one else two foreach i)^2;
  check "p" v[1] = 2;
tel

node M (x: int) returns (w: cval^2);
let
  w = (x foreach i)^2;
tel
"""


def test_subtype_obligations(tmp_path):
    path = tmp_path / "model.lus"
    path.write_text(model)
    args = common_args | {"--timeout": "30"}
    arg_list = [arg for pair in args.items() for arg in pair]
    proc = subprocess.run(
        [kind2_bin, *arg_list, str(path)],
        capture_output=True,
        text=True,
        timeout=run_timeout,
    )
    summaries = proc.stdout.split("Summary of Properties")[1:]
    lines = [l for s in summaries for l in s.splitlines() if l.startswith("SubType")]
    # The output of N, whose values are in cval
    assert any(l.startswith("SubType[L5C20]: valid") for l in lines)
    # The output of M, which may be out of cval
    assert any(l.startswith("SubType[L11C26]: invalid") for l in lines)
    # No obligation for the comprehension of N itself, at line 7
    assert not any(l.startswith("SubType[L7") for l in lines)
