"""Calls of a function with the same arguments in a node share one instance.

A function is a function of its arguments, so two calls of it with the same
arguments have the same outputs. Each call used to be compiled to an
instance of its own, with its own copy of the function's body and of its
checks. The second call now reuses the instance of the first, and the
function's checks appear once.

Calls of a node are not shared: a node is not a function of its arguments
(see falsifiable/node_calls_not_shared.lus).
"""

import json
import subprocess

from conftest import common_args, kind2_bin, run_timeout

model = """
function F (x: int) returns (y: int);
(*@contract
  assume "pos" x > 0;
  guarantee "gt" y > x;
*)
let
  y = x + 1;
tel

node main (a: int) returns (b: int);
(*@contract
  assume a > 0;
*)
let
  b = F(a) + F(a);
  check "sum" b > 2 * a;
tel
"""


def test_identical_calls_share_an_instance(tmp_path):
    path = tmp_path / "shared_function_calls.lus"
    path.write_text(model)
    arg_list = [arg for pair in common_args.items() for arg in pair]
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
    assert proc.returncode == 0, answers
    assert answers["sum"] == "valid"
    # One instance of F, so its assumption and guarantee are checked once
    callee_checks = sorted(name for name in answers if name.startswith("F["))
    assert len(callee_checks) == 2, callee_checks
    assert all(answers[name] == "valid" for name in callee_checks)
