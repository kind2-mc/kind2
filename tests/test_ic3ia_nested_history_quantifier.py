"""IC3IA does not falsify a valid property with a nested history quantifier.

A `history(x)` quantifier nested inside another quantifier, in a property whose
body holds for every value of the outer variable, left IC3IA with a quantified
system without arrays: the body simplifies to true and the history array is
sliced away, so the check that declines quantified formulas over arrays up
front does not apply. The refinement of the abstraction then went through
MathSAT, which answers quantified queries unsoundly, and IC3IA reported the
property invalid after 1 step; next to another property over the same history,
the analysis ended one time in three with a runtime failure of the invariant
manager, as the inductive step had proved the property (issue #1721). IC3IA now
declines the refinement with MathSAT and leaves the property unknown, the
interpolating solvers that support quantifiers prove it, and the default
engines agree on both properties.
"""

import json
import shutil
import subprocess
from pathlib import Path

import pytest

from conftest import common_args, ic3ia_args, ic3ia_solver, kind2_bin, run_timeout

regression = Path(__file__).parent / "regression" / "success"

# The property of the issue on its own: IC3IA must not falsify it
nested = regression / "ic3ia" / "declined" / "ic3ia_nested_history_quantifier.lus"

# The same property next to one with the history quantifier at the top level:
# the engines must not contradict each other
nested_and_top_level = regression / "history_nested_quantifier.lus"


def run(path, *extra):
    """The answers to the properties and the log messages by level of a run
    of Kind 2 on `path` with the common arguments and `extra`."""
    arg_list = [arg for pair in common_args.items() for arg in pair]
    proc = subprocess.run(
        [kind2_bin, "-json", *arg_list, *extra, str(path)],
        capture_output=True,
        text=True,
        timeout=run_timeout,
    )
    objs = json.loads(proc.stdout)
    logs = {}
    for obj in objs:
        if obj.get("objectType") == "log":
            logs.setdefault(obj.get("level"), []).append(obj["value"])
    answers = {
        obj["name"]: obj["answer"]["value"]
        for obj in objs
        if obj.get("objectType") == "property"
    }
    return answers, logs, proc.stdout + proc.stderr


def ic3ia_with(itp_solver):
    args = ic3ia_args | {"--smt_itp_solver": itp_solver}
    return [arg for pair in args.items() for arg in pair]


def no_failures(logs):
    return logs.get("error", []) == [] and logs.get("fatal", []) == []


@pytest.mark.skipif(
    shutil.which(ic3ia_solver) is None, reason=f"{ic3ia_solver} is not installed"
)
def test_mathsat_declines_the_nested_quantifier():
    answers, logs, out = run(nested, *ic3ia_with("MathSAT"))
    assert answers.get("P1") == "unknown", out
    assert no_failures(logs), out
    assert any(
        "for property P1: MathSAT does not support quantified formulas" in msg
        for msg in logs.get("warn", [])
    ), out


@pytest.mark.parametrize(
    "itp_solver, binary", [("Z3qe", "z3"), ("cvc5qe", "cvc5")]
)
def test_quantifier_solvers_prove_the_nested_quantifier(itp_solver, binary):
    if shutil.which(binary) is None:
        pytest.skip(f"{binary} is not installed")
    answers, logs, out = run(nested, *ic3ia_with(itp_solver))
    assert answers.get("P1") == "valid", out
    assert no_failures(logs), out


@pytest.mark.skipif(
    shutil.which(ic3ia_solver) is None, reason=f"{ic3ia_solver} is not installed"
)
def test_default_engines_agree_next_to_a_top_level_quantifier():
    # The interpolating solver of the issue, pinned so that the test does not
    # depend on which one the detection picks
    answers, logs, out = run(nested_and_top_level, "--smt_itp_solver", "MathSAT")
    assert answers.get("P1") == "valid", out
    assert answers.get("P2") == "valid", out
    assert no_failures(logs), out
