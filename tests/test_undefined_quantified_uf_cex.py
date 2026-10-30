"""A counterexample that relies on an undefined function under a quantifier
is not reported.

A call applied to quantified variables is compiled to an application of the
functional symbol of the callee, which LustreFunDefs defines. The definition
can still be left out: the solver does not take recursive definitions, or the
body of the function is not one a definition is built from, as for S below,
which passes an array literal to its recursive call. The array literal is
lifted into an array local defined at fixed indexes. The symbol is then
uninterpreted, and under the quantifier it is an arbitrary function of its
inputs. A defined function whose definition applies S, such as F below, is
just as arbitrary.

The property p holds, but BMC falsified it at k=0 with an arbitrary value of S
under the quantifier. The supervisor only dropped the counterexample when it
happened to reach the cutoff of the instance retained for the call, which no
part of the property constrains, so whether p was reported invalid or left
unknown depended on the model the solver gave, and changed from run to run.
Such a counterexample is now never reported: the property is left unknown,
and unrolling S further would not change that.

A counterexample whose violation does not depend on the values of S is not
held back: with the inputs of the counterexample, the property cannot hold
whatever S is.
"""

import json
import shutil
import subprocess

import pytest

from conftest import common_args, kind2_bin, run_timeout

rotate = """
-- The sum of the elements of a, after rotating it n times
function rec S(a: int^3; n: int) returns (s: int);
con
  decreases n;
noc
let
  s = when n <= 0 then a[0] + a[1] + a[2] else S([a[1], a[2], a[0]], n - 1);
tel
"""

# p holds: rotating an array does not change the sum of its elements
direct = rotate + """
node N(a: int^3) returns ();
let
  check "p" forall (n: int) S(a, n) = a[0] + a[1] + a[2];
tel
"""

# F has a definition, which applies S, which has none
through_defined = rotate + """
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

# Every counterexample to q and r has a[0] <= 0, which falsifies them
# whatever S is
independent = rotate + """
node N(a: int^3) returns ();
let
  assert a[0] <= 0;
  check "q" (forall (n: int) S(a, n) = a[0] + a[1] + a[2]) and a[0] > 0;
  check "r" a[0] > 0;
tel
"""

# The solvers that take quantified formulas, with the name of their
# executable
solvers = {"Z3": "z3", "cvc5": "cvc5"}


def run(tmp_path, model, solver, slice_nodes):
    if shutil.which(solvers[solver]) is None:
        pytest.skip(f"{solvers[solver]} is not installed")
    path = tmp_path / "undefined_quantified_uf_cex.lus"
    path.write_text(model)
    args = common_args | {
        "--timeout": "10",
        "--smt_solver": solver,
        "--slice_nodes": slice_nodes,
    }
    arg_list = [arg for pair in args.items() for arg in pair]
    # BMC alone: the counterexamples are what is checked
    proc = subprocess.run(
        [kind2_bin, "-json", *arg_list, "--enable", "BMC", str(path)],
        capture_output=True,
        text=True,
        timeout=run_timeout,
    )
    objs = json.loads(proc.stdout)
    logs = [obj["value"] for obj in objs if obj.get("objectType") == "log"]
    # A property left unknown keeps BMC running until the timeout
    errors = [
        obj["value"]
        for obj in objs
        if obj.get("objectType") == "log"
        and obj.get("level") in ("error", "fatal")
        and obj["value"] != "Wallclock timeout."
    ]
    assert errors == [], errors
    answers = {
        obj["name"]: obj["answer"]["value"]
        for obj in objs
        if obj.get("objectType") == "property"
    }
    return logs, answers


def relies_on(logs, function):
    return any(
        f"rely on an application of {function} " in log
        for log in logs
    )


@pytest.mark.parametrize("slice_nodes", ["on", "off"])
@pytest.mark.parametrize("solver", solvers)
def test_undefined_function_cex_is_not_reported(tmp_path, solver, slice_nodes):
    logs, answers = run(tmp_path, direct, solver, slice_nodes)
    assert relies_on(logs, "S"), logs
    assert answers.get("p") == "unknown", answers


@pytest.mark.parametrize("slice_nodes", ["on", "off"])
@pytest.mark.parametrize("solver", solvers)
def test_defined_function_applying_undefined_one(tmp_path, solver, slice_nodes):
    logs, answers = run(tmp_path, through_defined, solver, slice_nodes)
    assert any(
        "Function F is applied to quantified variables but its definition "
        "applies S" in log
        for log in logs
    ), logs
    # BMC does not always find a counterexample to hold back here: cvc5
    # finds none in time, with the definition of F under the quantifier
    assert answers.get("p") == "unknown", answers


@pytest.mark.parametrize("slice_nodes", ["on", "off"])
@pytest.mark.parametrize("solver", solvers)
def test_independent_violation_is_not_held_back(tmp_path, solver, slice_nodes):
    logs, answers = run(tmp_path, independent, solver, slice_nodes)
    # The counterexamples to q and r are not held back for S. They may still
    # be left unknown by the check of the cutoffs of the instance of S
    # retained for the call, which is a separate matter.
    assert not relies_on(logs, "S"), logs
    assert answers.get("q") in ("falsifiable", "unknown"), answers
    assert answers.get("r") in ("falsifiable", "unknown"), answers
