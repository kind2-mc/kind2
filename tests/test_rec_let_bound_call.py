"""A counterexample past the cutoff of a recursive function is evaluated along
the calls the instances of the function's definition execute.

The value of F(50) depends on the imported E, so the supervisor instantiates
the definition of F at 50, and the calls that instance applies are evaluated
in turn. The definition binds the argument of its recursive call in a let,
and the call used to be collected with the variable of the let as its
argument: the solver rejected the query that asked for its value, and the
counterexample was left undecided. The calls on the branch of an
if-then-else that the model does not take were collected as well: the
instance of F at 0 applies F at -50 on its other branch, and evaluating that
call went on past the end of the recursion until the rounds of evaluation ran
out. Either way, with no unrollings left, the falsifiable property was left
unknown.
"""

import json
import subprocess

from conftest import common_args, kind2_bin, run_timeout

model = """
function imported E (x: int) returns (z: int);

function rec F (n: int) returns (r: int);
(*@contract
  decreases n;
*)
let
  r = when n <= 0 then E(n) else F(n - 50);
tel

node main (n: int) returns (u: bool);
let
  u = true;
  check "p" n = 100 => F(n) <> 7;
tel
"""


def test_counterexample_past_cutoff_with_let_bound_call(tmp_path):
    path = tmp_path / "rec_let_bound_call.lus"
    path.write_text(model)
    args = common_args | {"--timeout": "60", "--rec_unrollings": "0"}
    arg_list = [arg for pair in args.items() for arg in pair]
    proc = subprocess.run(
        [kind2_bin, "-json", *arg_list, str(path)],
        capture_output=True,
        text=True,
        timeout=run_timeout,
    )
    answers = {
        obj["name"]: obj["answer"]["value"]
        for obj in json.loads(proc.stdout)
        if obj.get("objectType") == "property"
    }
    assert answers.get("p") == "falsifiable", answers
