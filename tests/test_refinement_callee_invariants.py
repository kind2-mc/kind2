"""A refinement assumes what the analysis of each refined node established.

The assumptions of an analysis are the invariants of the analysis before it.
Before a refinement, that is the analysis of the same node in which the
refined nodes were abstract, and an abstract node gets no assumptions, so the
invariants established by the analysis of a refined node, its guarantees
among them, were not passed on. The property of the model then needs an
invariant generator to rediscover the guarantee; with BMC and k-induction
only, it was left unknown. The first analysis falsifies it, and the documented
exit code counts every analysis, so this checks the answer of the refinement.
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
    / "refinement_callee_invariants.lus"
)


def test_refinement_assumes_callee_guarantee():
    args = common_args | {
        "--compositional": "true",
        "--modular": "true",
        "--timeout": "20",
    }
    arg_list = [arg for pair in args.items() for arg in pair]
    arg_list += ["--enable", "BMC", "--enable", "IND"]
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

    assert len(of_main) == 2, of_main
    assert of_main[0] == {"q": "falsifiable"}
    assert of_main[1] == {"q": "valid"}
