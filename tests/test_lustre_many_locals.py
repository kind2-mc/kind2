"""Kind 2 translates a node whose equations mention thousands of locals
in a time about linear in their number.

Two steps of the translation of a node took a time quadratic in its
number of locals:

- ordering the equations by dependency looked for the indexes of each
  state variable of an equation with a traversal of the equation of its
  own, although an equation with no array select gives none;
- for each stateless local, the translation of the transition relation
  looked for the variable at the previous instant in all the constraints
  generated so far, rather than keeping the variables it had already
  found.

A node with 6000 locals summed in one equation took about 200 s; it now
takes about 30 s. The cost going from quadratic to linear, the test uses
enough locals for the time limit to sit well between the two.
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
    timeout = 90
    args = common_args | {"--timeout": str(timeout)}
    arg_list = [arg for pair in args.items() for arg in pair]
    proc = run_kind2(
        [kind2_bin, "-json", *arg_list, "--enable", "BMC", str(path)],
        timeout=timeout + 60,
    )
    objs = json.loads(proc.stdout)
    answers = {
        obj["name"]: obj["answer"]["value"]
        for obj in objs
        if obj.get("objectType") == "property"
    }
    assert answers == {"fails": "falsifiable"}, proc.stdout
