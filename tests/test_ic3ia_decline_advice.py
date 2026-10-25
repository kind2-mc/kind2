"""The solver IC3IA suggests when it declines a system supports that system.

The interpolating solvers that eliminate quantifiers (Z3qe, cvc5qe) take no
abstract function, and the others (MathSAT, SMTInterpol) take no quantifier.
Each decline used to suggest the solvers of the other kind whatever the system
used, so that a quantified property in a node calling an imported function
sent the user from one solver to the next, with none that could answer. The
advice now names only the solvers that support the system, or says that none
does (review of #1843). The decline also names the property, and is decided
on the system the property is checked on, which slicing reduces to what the
property depends on, so that a solver it suggests can take that property.
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


# The abstract function is in the slice of `r` only, the quantifier in the
# slice of `q` only: each property has a solver that proves it
sliced = """
function imported f (x: int) returns (z: int);
node N (y: int) returns (w: int);
let
  w = f(y);
  assert y > 0;
  check "q" forall (j: int) (j = 0 => (true -> pre y > 0));
  check "r" w = f(y) and (true -> pre y > 0);
tel
"""

# Machine integers with integers, which MathSAT does not take, and an
# abstract function, which Z3qe does not take
machine_integers = """
function imported f (x: int) returns (z: int);
node N (y: int; b: uint8) returns (w: int);
let
  w = f(y);
  assert y > 0 and b > (uint8 0);
  check "p" (w = f(y)) and (true -> pre y > 0) and (b > (uint8 0) or y > 0);
tel
"""

arrays = """
node N (a: int^3) returns ();
let
  assert a[0] > 0;
  check "p" true -> pre a[0] > 0;
tel
"""

requires_z3 = pytest.mark.skipif(
    shutil.which("z3") is None, reason="z3 is not installed"
)
requires_mathsat = pytest.mark.skipif(
    shutil.which("mathsat") is None, reason="mathsat is not installed"
)


def run(path, itp_solver):
    """The warnings, the errors, the answers and the output of a run of IC3IA
    with `itp_solver` on `path`."""
    args = common_args | ic3ia_args | {"--smt_itp_solver": itp_solver}
    arg_list = [arg for pair in args.items() for arg in pair]
    proc = run_kind2([kind2_bin, "-json", *arg_list, str(path)])
    objs = json.loads(proc.stdout)
    answers = {
        obj["name"]: obj["answer"]["value"]
        for obj in objs
        if obj.get("objectType") == "property"
    }
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
    return warns, errors, answers, proc.stdout.decode() + proc.stderr.decode()


def warnings(path, itp_solver):
    warns, errors, _, out = run(path, itp_solver)
    return warns, errors, out


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


@requires_z3
@requires_mathsat
def test_advice_follows_the_slice(tmp_path):
    path = tmp_path / "model.lus"
    path.write_text(sliced)

    warns, errors, answers, out = run(path, "Z3qe")
    assert errors == [], out
    assert answers.get("q") == "valid", out
    assert answers.get("r") == "unknown", out
    assert any(
        "IC3IA (Z3qe) disabled for property r: system includes an abstract "
        "function. Use MathSAT or SMTInterpol instead." in msg
        for msg in warns
    ), out

    warns, errors, answers, out = run(path, "MathSAT")
    assert errors == [], out
    assert answers.get("r") == "valid", out
    assert answers.get("q") == "unknown", out
    assert any(
        "IC3IA (MathSAT) disabled for property q: MathSAT does not support "
        "quantified formulas, and the refinement of the abstraction needs them. "
        "Use Z3qe or cvc5qe instead." in msg
        for msg in warns
    ), out


@requires_z3
@requires_mathsat
def test_advice_with_machine_integers(tmp_path):
    path = tmp_path / "model.lus"
    path.write_text(machine_integers)
    for itp_solver, reason in [
        ("Z3qe", "system includes an abstract function."),
        (
            "MathSAT",
            "MathSAT does not support programs with both integers/reals and "
            "machine integers.",
        ),
    ]:
        warns, errors, out = warnings(path, itp_solver)
        assert errors == [], out
        assert any(
            f"IC3IA ({itp_solver}) disabled for property p: {reason} "
            "No other interpolating solver supports this system" in msg
            for msg in warns
        ), out


@requires_z3
def test_one_warning_per_property(tmp_path):
    # IC3IA runs forward and backward with Z3qe, and both instances used to
    # report the decline
    path = tmp_path / "model.lus"
    path.write_text(arrays)
    warns, errors, out = warnings(path, "Z3qe")
    assert errors == [], out
    declines = [msg for msg in warns if "IC3IA (Z3qe) disabled" in msg]
    assert len(declines) == 1, out
