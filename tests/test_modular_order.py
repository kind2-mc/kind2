"""A modular analysis analyzes every node after the nodes it calls.

In the model, main calls A and then B, and A also calls B. B used to be
skipped when A was reached, because it was already queued as a subsystem of
main, so A was analyzed first. B had no result yet, and the call to B in A
could not be refined: the property of A stayed falsified, where analyzing B
first lets a refinement of A prove it. The documented exit code counts every
analysis, and the property is falsified under B's contract in either order,
so the exit code does not tell the two apart. This checks the order of the
analyses and the answer of the last analysis of A.
"""

import json
import subprocess
from pathlib import Path

from conftest import common_args, kind2_bin, run_timeout

model = (
    Path(__file__).parent
    / "regression"
    / "falsifiable"
    / "compositional"
    / "modular"
    / "modular_order.lus"
)


def test_callee_is_analyzed_before_caller():
    args = common_args | {"--compositional": "true", "--modular": "true"}
    arg_list = [arg for pair in args.items() for arg in pair]
    run = subprocess.run(
        [kind2_bin, "-json", *arg_list, str(model)],
        capture_output=True,
        text=True,
        timeout=run_timeout,
    )

    # The top node of each analysis, in order, and the answers to the
    # properties of each analysis
    analyses = []
    for obj in json.loads(run.stdout):
        if obj.get("objectType") == "analysisStart":
            analyses.append((obj["top"], {}))
        elif obj.get("objectType") == "property":
            analyses[-1][1][obj["name"]] = obj["answer"]["value"]

    tops = [top for top, _ in analyses]
    assert tops.index("B") < tops.index("A"), tops

    # The last analysis of A is a refinement, which proves "a"
    last_of_a = [answers for top, answers in analyses if top == "A"][-1]
    assert last_of_a == {"a": "valid"}
