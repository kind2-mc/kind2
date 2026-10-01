"""A call to a recursive function that reads global constants is evaluated
under the values of the constants in the counterexample.

A counterexample that reaches calls past the unrollings is checked by
evaluating the calls at their concrete arguments. The value of a call whose
function reads a global constant depends on the constant, and is evaluated
under the value the counterexample gives it, which the check fixes: a check
that does not hold is falsified however deep its calls are, while one that
holds is not. A falsifiable run counts every analysis in its exit code, so
this checks the answers of each property.
"""

import json
import subprocess
from pathlib import Path

import pytest

from conftest import common_args, kind2_bin, run_timeout

falsifiable = Path(__file__).parent / "regression" / "falsifiable"


COMPOSITIONAL = {"--compositional": "true", "--modular": "true"}


def answers(model, mode):
    args = common_args | mode
    arg_list = [arg for pair in args.items() for arg in pair]
    run = subprocess.run(
        [kind2_bin, "-json", *arg_list, str(model)],
        capture_output=True,
        text=True,
        timeout=run_timeout,
    )
    return {
        obj["name"]: obj["answer"]["value"]
        for obj in json.loads(run.stdout)
        if obj.get("objectType") == "property" and "[" not in obj["name"]
    }


@pytest.mark.parametrize(
    "model, mode",
    [
        ("rec_eval_global_constants.lus", {}),
        ("compositional/modular/rec_eval_global_constants.lus", COMPOSITIONAL),
    ],
)
@pytest.mark.parametrize("arrays", [{}, {"--smt_arrays": "true"}])
def test_calls_evaluated_under_constants(model, mode, arrays):
    found = answers(falsifiable / model, mode | arrays)
    assert found["sum_wrong"] == "falsifiable", found
    assert found["shift_wrong"] == "falsifiable", found
    assert found["sum_right"] != "falsifiable", found
    assert found["shift_right"] != "falsifiable", found


def test_right_checks_proved_with_enough_unrollings():
    found = answers(
        falsifiable / "rec_eval_global_constants.lus",
        {"--rec_unrollings": "12"},
    )
    assert found == {
        "sum_wrong": "falsifiable",
        "shift_wrong": "falsifiable",
        "sum_right": "valid",
        "shift_right": "valid",
    }, found
