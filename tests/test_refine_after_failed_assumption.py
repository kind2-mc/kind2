"""A node is refined even when an assumption of a callee was falsified.

The strategy used to skip the refinement of a node whenever the assumptions
of one of its callees could not be proved. The guarantees of an abstracted
callee are only asserted while its assumptions have held, so what was proved
under the abstraction still holds after refining a callee proved correct, and
the refinement may prove the assumption itself. The first analysis falsifies
the assumption, and the documented exit code counts every analysis, so the
exit code does not tell whether the refinement ran. This checks the answers
of the last analysis of main.
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
    / "refine_after_failed_assumption.lus"
)


def test_refinement_proves_assumption():
    args = common_args | {"--compositional": "true", "--modular": "true"}
    arg_list = [arg for pair in args.items() for arg in pair]
    run = subprocess.run(
        [kind2_bin, "-json", *arg_list, str(model)],
        capture_output=True,
        text=True,
        timeout=run_timeout,
    )

    # The answers to the properties of each analysis of main
    of_main = []
    top = None
    for obj in json.loads(run.stdout):
        if obj.get("objectType") == "analysisStart":
            top = obj["top"]
            if top == "main":
                of_main.append({})
        elif obj.get("objectType") == "property" and top == "main":
            of_main[-1][obj["name"]] = obj["answer"]["value"]

    assert len(of_main) > 1, "main was not refined"
    assert set(of_main[-1].values()) == {"valid"}, of_main[-1]
