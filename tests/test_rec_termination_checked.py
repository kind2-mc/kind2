"""The analysis of a recursive function checks the termination of its calls.

The termination checks of a recursive call are generated with the call, and
slicing used to remove a call that no property or guarantee depends on: a
function with no contract and no property had its analysis skipped, as its
system had no property left. A run with no property is successful, so this
checks that the analysis of each function has the checks of its calls, in a
modular analysis, compositional or not.
"""

import json
import subprocess
from pathlib import Path

import pytest

from conftest import common_args, kind2_bin, run_timeout

model = (
    Path(__file__).parent
    / "regression"
    / "success"
    / "modular"
    / "rec_termination_no_contract.lus"
)


@pytest.mark.parametrize("compositional", ["false", "true"])
def test_termination_checked_without_contract(compositional):
    args = common_args | {"--modular": "true", "--compositional": compositional}
    arg_list = [arg for pair in args.items() for arg in pair]
    run = subprocess.run(
        [kind2_bin, "-json", *arg_list, str(model)],
        capture_output=True,
        text=True,
        timeout=run_timeout,
    )
    answers = {}
    current = None
    for obj in json.loads(run.stdout):
        if obj.get("objectType") == "analysisStart":
            current = obj["top"]
            answers[current] = {}
        elif obj.get("objectType") == "property" and current is not None:
            answers[current][obj["name"]] = obj["answer"]["value"]

    for function in ["IsEven", "IsOdd", "Fact"]:
        # The analysis of a function also has the properties of its
        # callees, such as the subrange checks of their inputs
        checks = {
            name: answer
            for name, answer in answers.get(function, {}).items()
            if name.startswith(("bounded_check[", "decrease_check["))
        }
        kinds = {name.split("[")[0] for name in checks}
        assert kinds == {"bounded_check", "decrease_check"}, (function, answers)
        assert set(checks.values()) == {"valid"}, (function, checks)
