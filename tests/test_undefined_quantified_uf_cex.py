"""A counterexample that relies on an undefined function under a quantifier
is not reported.

A call applied to quantified variables is compiled to an application of the
functional symbol of the callee, which LustreFunDefs defines. The definition
can still be left out: the solver does not take recursive definitions, or the
body of the function is not one a definition is built from, as for S below,
which passes an array literal to its recursive call. The array literal is
lifted into an array local defined at fixed indexes. The symbol is then
uninterpreted, and under the quantifier it is an arbitrary function of its
inputs.

The property p holds, but BMC falsified it at k=0 with an arbitrary value of S
under the quantifier. The supervisor only dropped the counterexample when it
happened to reach the cutoff of the instance retained for the call, which no
part of the property constrains, so whether p was reported invalid or left
unknown depended on the model the solver gave, and changed from run to run.
Such a counterexample is now never reported: the property is left unknown,
and unrolling S further would not change that.
"""

import json
import shutil
import subprocess

import pytest

from conftest import common_args, kind2_bin, run_timeout

model = """
-- The sum of the elements of a, after rotating it n times
function rec S(a: int^3; n: int) returns (s: int);
con
  decreases n;
noc
let
  s = when n <= 0 then a[0] + a[1] + a[2] else S([a[1], a[2], a[0]], n - 1);
tel

node N(a: int^3) returns ();
let
  -- Holds: rotating an array does not change the sum of its elements
  check "p" forall (n: int) S(a, n) = a[0] + a[1] + a[2];
tel
"""

# The solvers that take quantified formulas, with the name of their
# executable
solvers = {"Z3": "z3", "cvc5": "cvc5"}


@pytest.mark.parametrize("slice_nodes", ["on", "off"])
@pytest.mark.parametrize("solver", solvers)
def test_undefined_quantified_uf_cex_is_not_reported(tmp_path, solver, slice_nodes):
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
    proc = subprocess.run(
        [kind2_bin, "-json", *arg_list, str(path)],
        capture_output=True,
        text=True,
        timeout=run_timeout,
    )
    objs = json.loads(proc.stdout)
    logs = [obj for obj in objs if obj.get("objectType") == "log"]
    # p is left unknown, and the analysis runs until the timeout
    errors = [
        log["value"]
        for log in logs
        if log.get("level") in ("error", "fatal")
        and log["value"] != "Wallclock timeout."
    ]
    assert errors == [], errors
    # BMC falsifies p at k=0 with S arbitrary under the quantifier, and the
    # supervisor drops the counterexample
    assert any(
        "Counterexamples rely on an application of S" in log["value"]
        for log in logs
    ), logs
    answers = {
        obj["name"]: obj["answer"]["value"]
        for obj in objs
        if obj.get("objectType") == "property"
    }
    assert answers.get("p") == "unknown", answers
