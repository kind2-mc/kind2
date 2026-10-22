"""The invariants of a callee hold while its assumptions have held.

The analysis of a node as the top system asserts its assumptions, so the
invariants it establishes only hold of the node while its assumptions have
held. In a modular analysis they are given to the node in the analyses of its
callers, and they used to become invariants of the node there without that
guard: the invariant generator lifted them into the caller, and a property of
a caller that violates the assumptions could be proved although it is false.
The assumption is falsified in any case, and the exit code counts every
analysis, so this checks that the property is never proved. Without trivial
candidate pruning, the unguarded invariant is lifted as it is.
"""

import json
import subprocess
from pathlib import Path

import pytest

from conftest import common_args, kind2_bin, run_timeout

model = (
    Path(__file__).parent
    / "regression"
    / "falsifiable"
    / "modular"
    / "callee_invariants_violated_assumption.lus"
)


@pytest.mark.parametrize("compositional", ["false", "true"])
def test_false_property_not_proved(compositional):
    args = common_args | {
        "--modular": "true",
        "--compositional": compositional,
        "--invgen_prune_trivial": "false",
        # The counterexample to "p" is 1000 steps long, so that BMC does not
        # find it before the unguarded invariant is lifted. Finding it takes
        # a few seconds, more on slower machines.
        "--timeout": "30",
    }
    arg_list = [arg for pair in args.items() for arg in pair]
    run = subprocess.run(
        [kind2_bin, "-json", *arg_list, str(model)],
        capture_output=True,
        text=True,
        timeout=run_timeout,
    )

    answers = []
    top = None
    for obj in json.loads(run.stdout):
        if obj.get("objectType") == "analysisStart":
            top = obj["top"]
        elif (
            obj.get("objectType") == "property"
            and top == "main"
            and obj.get("name") == "p"
        ):
            answers.append(obj["answer"]["value"])

    assert answers, "main was not analyzed"
    assert "valid" not in answers, answers
