"""The solver IC3IA suggests when it declines a system supports that system.

The interpolating solvers that eliminate quantifiers (Z3qe, cvc5qe) take no
abstract function, and the others (MathSAT, SMTInterpol) take no quantifier.
Each decline used to suggest the solvers of the other kind whatever the system
used, so that a quantified property in a node calling an imported function
sent the user from one solver to the next, with none that could answer. The
advice now names only the solvers that support the system, or says that none
does (review of #1843). The decline also names the property.
"""

import json
import shutil

import pytest

from conftest import common_args, ic3ia_args, kind2_bin, run_kind2

both = """
function imported f (x: int) returns (z: int);
node N (y: int) returns (w: int);
let
  w = f(y);
  assert y > 0;
  check "p" (w = f(y)) and forall (j: int) (j = 0 => (true -> pre y > 0));
tel
"""

abstract_only = """
function imported f (x: int) returns (z: int);
node N (y: int) returns (w: int);
let
  w = f(y);
  check "p" w = f(y);
tel
"""


def warnings(path, itp_solver):
    args = common_args | ic3ia_args | {"--smt_itp_solver": itp_solver}
    arg_list = [arg for pair in args.items() for arg in pair]
    proc = run_kind2([kind2_bin, "-json", *arg_list, str(path)])
    objs = json.loads(proc.stdout)
    warns = [
        obj["value"]
        for obj in objs
        if obj.get("objectType") == "log" and obj.get("level") == "warn"
    ]
    errors = [
        obj["value"]
        for obj in objs
        if obj.get("objectType") == "log" and obj.get("level") in ("error", "fatal")
    ]
    return warns, errors, proc.stdout.decode() + proc.stderr.decode()


@pytest.mark.skipif(shutil.which("z3") is None, reason="z3 is not installed")
@pytest.mark.parametrize(
    "model, advice",
    [
        (both, "No other interpolating solver supports this system"),
        (abstract_only, "Use MathSAT or SMTInterpol instead."),
    ],
    ids=["quantified", "unquantified"],
)
def test_abstract_function_advice(tmp_path, model, advice):
    path = tmp_path / "model.lus"
    path.write_text(model)
    warns, errors, out = warnings(path, "Z3qe")
    assert errors == [], out
    assert any(
        "IC3IA (Z3qe) disabled for property p: system includes an abstract "
        "function. " + advice in msg
        for msg in warns
    ), out


@pytest.mark.skipif(
    shutil.which("mathsat") is None, reason="mathsat is not installed"
)
def test_quantifier_advice(tmp_path):
    path = tmp_path / "model.lus"
    path.write_text(both)
    warns, errors, out = warnings(path, "MathSAT")
    assert errors == [], out
    assert any(
        "IC3IA (MathSAT) disabled for property p: MathSAT does not support "
        "quantified formulas, and the refinement of the abstraction needs them. "
        "No other interpolating solver supports this system" in msg
        for msg in warns
    ), out
