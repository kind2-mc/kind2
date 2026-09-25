"""A caller is refined once the callee's contract is proved, and only then.

A refinement keeps what the caller's analysis proved with the callee
abstracted by its contract, which holds of the callee's implementation once
the guarantees are proved. The refinement used to require every property of
the callee's analysis to be proved, local checks included, and a failed check
kept the caller from being refined. For a recursive function, the guarantees
are proved with the recursive calls abstracted by the contract, which only
the termination checks justify, so those must be proved as well. The runs
are falsifiable either way, and the documented exit code counts every
analysis, so this checks the analyses of the caller.
"""

import json
import subprocess
from pathlib import Path

from conftest import common_args, kind2_bin, run_timeout

models = (
    Path(__file__).parent / "regression" / "falsifiable" / "compositional" / "modular"
)


def answers_of_main(model):
    args = common_args | {"--compositional": "true", "--modular": "true"}
    arg_list = [arg for pair in args.items() for arg in pair]
    run = subprocess.run(
        [kind2_bin, "-json", *arg_list, str(models / model)],
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


def test_refined_despite_failed_local_check():
    of_main = answers_of_main("refinement_failed_local_check.lus")
    assert [answers["p"] for answers in of_main] == ["falsifiable", "valid"]


def test_not_refined_when_termination_fails():
    of_main = answers_of_main("refinement_failed_termination.lus")
    assert [answers["q"] for answers in of_main] == ["falsifiable"]
