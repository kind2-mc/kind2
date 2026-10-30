"""A call applied to quantified variables is rejected when its function gets
no definition at the SMT level.

Such a call is compiled to an application of the functional symbol of the
callee, which only its definition gives a meaning to. The front end accepts
the call for a function a definition is to be built for, but LustreFunDefs
can still leave the definition out: an array literal or an array repetition
passed to a call is lifted into a local defined element by element, which no
definition is built from, and a definition that applies a function of another
recursive group applies it whether or not that function is defined. Under
the quantifier the symbol was then an arbitrary function of its inputs, and a
property that holds was reported falsifiable or not, depending on the model
the solver gave. The call is now rejected, as it is with a solver that does
not take recursive definitions.
"""

import json
import shutil
import subprocess

import pytest

from conftest import common_args, kind2_bin, run_timeout


def rotate(argument):
    return f"""
function rec S(a: int^3; n: int) returns (s: int);
con
  decreases n;
noc
let
  s = when n <= 0 then a[0] + a[1] + a[2] else S({argument}, n - 1);
tel
"""


direct = """
node N(a: int^3) returns ();
let
  check "p" forall (n: int) S(a, n) = a[0] + a[1] + a[2];
tel
"""

# F has a definition, which applies S, which has none
through_defined = """
function rec F(a: int^3; n: int) returns (s: int);
con
  decreases n;
noc
let
  s = when n <= 0 then S(a, 2) else F(a, n - 1);
tel

node N(a: int^3) returns ();
let
  check "p" forall (n: int) F(a, n) = a[0] + a[1] + a[2];
tel
"""

# Each solver, with the name of its executable
solvers = {"Z3": "z3", "cvc5": "cvc5", "Yices2": "yices-smt2"}


def run(tmp_path, model, solver):
    if shutil.which(solvers[solver]) is None:
        pytest.skip(f"{solvers[solver]} is not installed")
    path = tmp_path / "quantified_call_undefined_function.lus"
    path.write_text(model)
    args = common_args | {"--timeout": "20", "--smt_solver": solver}
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
    answers = {
        obj["name"]: obj["answer"]["value"]
        for obj in objs
        if obj.get("objectType") == "property"
    }
    return errors, answers


@pytest.mark.parametrize("solver", ["Z3", "cvc5"])
@pytest.mark.parametrize(
    "model, function, reason",
    [
        (rotate("[a[1], a[2], a[0]]") + direct, "S", "is defined element by element"),
        (rotate("a[1]^3") + direct, "S", "is defined element by element"),
        (rotate("[a[1], a[2], a[0]]") + through_defined, "F",
         "its definition applies 'S'"),
    ],
    ids=["array_literal", "array_repetition", "through_defined"],
)
def test_call_is_rejected(tmp_path, solver, model, function, reason):
    errors, answers = run(tmp_path, model, solver)
    assert any(
        f"Function '{function}' cannot be applied to quantified variables" in e
        and reason in e
        for e in errors
    ), errors
    assert answers == {}, answers


def test_call_is_rejected_without_recursive_definitions(tmp_path):
    errors, answers = run(tmp_path, rotate("a") + direct, "Yices2")
    assert any(
        "Function 'S' cannot be applied to quantified variables: recursive "
        "functions are not defined at the SMT level with the current solver"
        in e
        for e in errors
    ), errors
    assert answers == {}, answers


@pytest.mark.parametrize("solver", ["Z3", "cvc5"])
def test_defined_call_is_accepted(tmp_path, solver):
    # S passes its array input as it is, and is defined
    errors, answers = run(tmp_path, rotate("a") + direct, solver)
    assert not any("cannot be applied to quantified variables" in e for e in errors), errors
    assert "p" in answers, answers
