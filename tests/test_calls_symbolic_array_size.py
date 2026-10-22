"""Calls to functions over arrays of symbolic size are sent to the solver in
terms of the caller's symbols (issue #1611).

The size of an array input or output of a function can be a constant input
of the function. The bounds of the outputs of a call, which an equality on
the call compares the outputs within, and the bounds of the array arguments
in the congruence instances of an imported or abstracted function used to
refer to the constant input of the callee, a symbol the solver never sees in
the caller. The engines that sent them failed with an undeclared symbol, and
true properties were left unknown. Whichever engine fails, the default
engines may still answer, so each model is run with BMC, k-induction and
IC3IA only, with each solver, and no engine may fail.
"""

import json
import shutil
import subprocess

import pytest

from conftest import common_args, kind2_bin, run_timeout

ID_EQ = """
function Id(const k: int; a: int^k) returns (b: int^k);
let
  b = a;
tel

node N(a: int^2) returns ();
let
  check "id_eq" Id(2, a) = a;
tel
"""

IMPORTED = """
function imported P(const L: int; a: int^L) returns (r: bool);
(*@contract
  guarantee r = (a[0] >= 0);
*)

node N(const L: int; a: int^L) returns ();
var c: int;
let
  c = 0 -> pre c + 1;
  check "imported" P(L, a);
  check "counter" c >= 0;
tel
"""

REC = """
function rec Sum(const L: int; a: int^L; i: int) returns (s: int);
(*@contract
  decreases i;
*)
let
  s = if i <= 0 or i > L then 0 else a[i-1] + Sum(L, a, i-1);
tel

node N(const L: int; a: int^L) returns ();
var c: int;
let
  c = 0 -> pre c + 1;
  check "rec" Sum(L, a, 0) = 0;
  check "counter" c >= 0;
tel
"""


def run(tmp_path, model, solver):
    path = tmp_path / "model.lus"
    path.write_text(model)
    args = common_args | {"--smt_solver": solver}
    arg_list = [arg for pair in args.items() for arg in pair]
    run = subprocess.run(
        [kind2_bin, "-json", "--enable", "BMC", "--enable", "IND",
         "--enable", "IC3IA", *arg_list, str(path)],
        capture_output=True,
        text=True,
        timeout=run_timeout,
    )
    output = json.loads(run.stdout)
    failures = [
        obj["value"]
        for obj in output
        if obj.get("objectType") == "log"
        and obj.get("level") in ("error", "fatal")
    ]
    answers = {
        obj["name"]: obj["answer"]["value"]
        for obj in output
        if obj.get("objectType") == "property" and "[" not in obj["name"]
    }
    return failures, answers


@pytest.mark.parametrize("solver", ["Z3", "cvc5"])
@pytest.mark.parametrize(
    "model, expected",
    [
        (ID_EQ, {"id_eq": "valid"}),
        (IMPORTED, {"imported": "falsifiable", "counter": "valid"}),
        (REC, {"rec": "valid", "counter": "valid"}),
    ],
    ids=["call_equality", "imported_call", "rec_call"],
)
def test_no_undeclared_symbol(tmp_path, model, expected, solver):
    if shutil.which(solver.lower()) is None:
        pytest.skip(f"{solver} is not installed")
    failures, answers = run(tmp_path, model, solver)
    assert failures == [], failures
    assert answers == expected, answers
