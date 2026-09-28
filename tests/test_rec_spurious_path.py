"""A counterexample whose path relies on a call past the unrollings is not
reported.

Outside of compositional analyses, the recursive calls past the unrollings of
a function are left unconstrained. The supervisor used to take a
counterexample reaching such a call as genuine when, with the inputs of the
counterexample fixed, the property could not hold whatever the values of the
calls. That misses what the path itself relies on: here the assumption of
Obs, IsOdd(a), is what makes an even a possible, and it only holds of an even
a because the call past the unrollings is unconstrained. The property holds
of the functions as they are, and must not be reported falsifiable; the
supervisor now evaluates the calls the counterexample relies on before it
reports it.

The model is not in the regression tree: the property needs induction over
the mutual recursion, so the run leaves it unknown.
"""

import json
import subprocess

from conftest import common_args, kind2_bin, run_timeout

model = """
type Nat = subrange [0,*] of int;

function rec IsEven(n: Nat) returns (e: bool);
(*@contract
  decreases n;
*)
let
  e = when n = 0 then true else IsOdd(n - 1);
tel

function rec IsOdd(n: Nat) returns (o: bool);
(*@contract
  decreases n;
*)
let
  o = when n = 0 then false else IsEven(n - 1);
tel

node Obs(a: Nat) returns ();
(*@contract
  assume IsOdd(a);
*)
let
  check "odd" a mod 2 = 1;
tel
"""


def test_counterexample_relying_on_unconstrained_call_not_reported(tmp_path):
    path = tmp_path / "rec_spurious_path.lus"
    path.write_text(model)
    args = common_args | {"--timeout": "60", "--rec_unrollings": "3"}
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
    assert answers.get("odd") != "falsifiable", answers
    assert "falsifiable" not in answers.values(), answers
    assert proc.returncode != 40, answers
