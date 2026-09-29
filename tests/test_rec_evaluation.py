"""A call to a recursive function proved terminating is evaluated.

In a compositional and modular analysis, once the analysis of a recursive
function has proved the termination checks of its recursive calls, a call to
the function at constant arguments is evaluated while the system of the
caller is built, and its value given to the solver. The caller then needs no
refinement to know the value of the call, although the contract of the
function, which abstracts it, does not give it. A falsifiable run counts every
analysis in its exit code, so this checks the answers of each analysis of
main.
"""

import json
import subprocess
from pathlib import Path

import pytest

from conftest import common_args, kind2_bin, run_timeout

regression = Path(__file__).parent / "regression"


def answers_of_main(model):
    args = common_args | {"--compositional": "true", "--modular": "true"}
    arg_list = [arg for pair in args.items() for arg in pair]
    run = subprocess.run(
        [kind2_bin, "-json", *arg_list, str(regression / model)],
        capture_output=True,
        text=True,
        timeout=run_timeout,
    )
    of_main = []
    current = None
    for obj in json.loads(run.stdout):
        if obj.get("objectType") == "analysisStart":
            current = obj["top"]
            if current == "main":
                of_main.append({})
        elif obj.get("objectType") == "property" and current == "main":
            of_main[-1][obj["name"]] = obj["answer"]["value"]
    return of_main


def test_evaluated_calls_need_no_refinement():
    of_main = answers_of_main(
        "success/compositional/modular/rec_eval_constant_args.lus"
    )
    assert len(of_main) == 1, of_main
    assert set(of_main[0].values()) == {"valid"}, of_main[0]


def test_evaluated_value_is_the_function_value():
    of_main = answers_of_main(
        "falsifiable/compositional/modular/rec_eval_constant_args.lus"
    )
    assert of_main[0]["right"] == "valid", of_main[0]
    assert of_main[0]["wrong"] == "falsifiable", of_main[0]


def test_function_not_proved_terminating_is_not_evaluated():
    of_main = answers_of_main(
        "falsifiable/compositional/modular/rec_eval_not_terminating.lus"
    )
    assert of_main == [{"f4": "falsifiable"}], of_main
