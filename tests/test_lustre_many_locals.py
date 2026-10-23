"""Kind 2 translates a node whose equations mention thousands of locals
in a time several times shorter than it used to.

Two steps of the translation of a node took a time quadratic in its
number of locals:

- ordering the equations by dependency looked for the indexes of each
  state variable of an equation with a traversal of the equation of its
  own, although an equation with no array select gives none;
- for each stateless local, the translation of the transition relation
  looked for the variable at the previous instant in all the constraints
  generated so far, rather than keeping the variables it had already
  found.

The whole run still grows faster than linearly, so the test cannot tell
the two apart by how the time grows, only by the time itself. On a fast
machine (BMC, run to its first answer):

| locals | now   | before |
|--------|-------|--------|
| 3000   | 6 s   | 36 s   |
| 6000   | 28 s  | 199 s  |
| 8000   | 56 s  | 420 s  |

The ratio stays about 7 at every size, so more locals do not widen the
margin. The slowest CI runner (macOS on x86_64) takes about three times
as long, about 90 s with 6000 locals. A limit of 135 s leaves about 1.5
times the run on that runner, and is about 1.5 times shorter than the
old translation on a fast machine.
"""

import json

from conftest import common_args, kind2_bin, run_kind2


def flat_sum(n):
    """A node with n stateless locals, b_i = x * i, summed in the
    equation of the output"""
    locals_ = ", ".join(f"b{i}" for i in range(1, n + 1))
    eqs = "\n".join(f"  b{i} = x * {i};" for i in range(1, n + 1))
    total = " + ".join(f"b{i}" for i in range(1, n + 1))
    return f"""
node main (x: int) returns (y: int);
var {locals_}: int;
let
{eqs}
  y = {total};
  check "fails" y <> {n * (n + 1) // 2};
tel
"""


def test_many_locals_in_one_equation(tmp_path):
    path = tmp_path / "sum.lus"
    path.write_text(flat_sum(6000))
    timeout = 135
    args = common_args | {"--timeout": str(timeout)}
    arg_list = [arg for pair in args.items() for arg in pair]
    proc = run_kind2(
        [kind2_bin, "-json", *arg_list, "--enable", "BMC", str(path)],
        timeout=timeout + 60,
    )
    # The run must end before the time limit: a timeout while the
    # counterexample is printed can still leave a falsifiable answer
    assert b"Wallclock timeout" not in proc.stdout, proc.stdout
    objs = json.loads(proc.stdout)
    props = [obj for obj in objs if obj.get("objectType") == "property"]
    answers = {obj["name"]: obj["answer"]["value"] for obj in props}
    assert answers == {"fails": "falsifiable"}, proc.stdout
    assert all(obj.get("counterExample") for obj in props), proc.stdout
