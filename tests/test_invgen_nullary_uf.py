"""The invariant generator does not mine candidate terms over a constant
uninterpreted function.

When a function without inputs is abstracted by its contract, its output is
a constant uninterpreted function, such as U.r.__function_of_inputs, in the
transition relation of its callers. The integer miner took the constant as a
candidate term, but the models of the invariant generator only give values to
variables: the first model the generator evaluated the candidate in raised
Invalid_argument("num_of_value for term U.r.__function_of_inputs"), and the
invariant generator stopped. Here the property needs an invariant, so the
generator runs until it is evaluated.
"""

import json
import subprocess

from conftest import common_args, kind2_bin, run_timeout

model = """
type Nat = subrange [0,*] of int;

function U() returns (r: Nat);
let
  r = 0;
tel

node G() returns (x: int);
let
  x = U() -> pre x + 2;
  check "odd" x <> 1;
tel
"""


def test_constant_uf_not_mined(tmp_path):
    path = tmp_path / "model.lus"
    path.write_text(model)
    # The default timeout: the property is proved at once, but a shorter
    # one was reached on a slow runner, where "Wallclock timeout." is logged
    # as an error
    args = common_args | {
        "--modular": "true",
        "--compositional": "true",
    }
    arg_list = [arg for pair in args.items() for arg in pair]
    proc = subprocess.run(
        [kind2_bin, "-json", *arg_list, str(path)],
        capture_output=True,
        text=True,
        timeout=run_timeout,
    )
    objs = json.loads(proc.stdout)
    errors = [
        obj["value"]
        for obj in objs
        if obj.get("objectType") == "log"
        and obj.get("level") in ("error", "fatal")
    ]
    assert errors == [], errors
    answers = {
        obj["name"]: obj["answer"]["value"]
        for obj in objs
        if obj.get("objectType") == "property"
    }
    assert answers.get("odd") != "falsifiable", answers
