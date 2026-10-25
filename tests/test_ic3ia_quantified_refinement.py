"""IC3IA does not refine a quantified system with a solver that cannot.

MathSAT does not support quantifiers, and its SMT-LIB front end does not
reject them: a query over a formula with a quantifier comes back satisfiable,
with a model that violates the formula. IC3IA took such an answer for a
genuine counterexample, and reported a valid quantified property falsifiable
whenever its proof needed the abstraction refined (issue #1840). It now
declines the system when the refinement would go through MathSAT (or OpenSMT,
which refuses quantifiers outright), and leaves the property unknown. A
quantified property it settles without refining is still proved with MathSAT,
and the interpolating solvers that support quantifiers prove the others. As
the main solver, MathSAT is refused for such a system, as OpenSMT is: every
engine took its answers for genuine.
"""

import json
import shutil
import subprocess
from pathlib import Path

import pytest

from conftest import common_args, ic3ia_args, ic3ia_solver, kind2_bin, run_timeout

# A property whose proof needs the predicate `y > 0`, which only an
# interpolant gives
needs_refinement = (
    Path(__file__).parent
    / "regression"
    / "success"
    / "ic3ia"
    / "declined"
    / "ic3ia_quantified_pre_sound.lus"
)

# The same fact about the current state, which the initial predicates settle
# without an interpolant
needs_none = """
node N (y: int) returns ();
let
  assert y > 0;
  check "p" forall (j: int) y > 0;
tel
"""


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
def test_mathsat_declines_the_refinement():
    answers, logs, out = run(needs_refinement, *ic3ia_with("MathSAT"))
    assert answers.get("p") == "unknown", out
    assert no_failures(logs), out
    assert any(
        "for property p: MathSAT does not support quantified formulas" in msg
        for msg in logs.get("warn", [])
    ), out


@pytest.mark.skipif(
    shutil.which(ic3ia_solver) is None, reason=f"{ic3ia_solver} is not installed"
)
def test_mathsat_proves_without_refinement(tmp_path):
    path = tmp_path / "model.lus"
    path.write_text(needs_none)
    answers, logs, out = run(path, *ic3ia_with("MathSAT"))
    assert answers.get("p") == "valid", out
    assert no_failures(logs), out


@pytest.mark.parametrize(
    "itp_solver, binary", [("Z3qe", "z3"), ("cvc5qe", "cvc5")]
)
def test_quantifier_solvers_prove(itp_solver, binary):
    if shutil.which(binary) is None:
        pytest.skip(f"{binary} is not installed")
    answers, logs, out = run(needs_refinement, *ic3ia_with(itp_solver))
    assert answers.get("p") == "valid", out
    assert no_failures(logs), out


@pytest.mark.skipif(
    shutil.which(ic3ia_solver) is None, reason=f"{ic3ia_solver} is not installed"
)
def test_mathsat_refused_as_main_solver():
    answers, logs, out = run(
        needs_refinement,
        "--smt_solver", "MathSAT", "--enable", "BMC", "--enable", "IND",
    )
    assert answers.get("p") != "falsifiable", out
    assert any(
        "MathSAT does not support quantifiers" in msg
        for msgs in logs.values() for msg in msgs
    ), out
