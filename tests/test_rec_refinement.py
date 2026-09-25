"""A refinement defines a recursive function in place of its contract.

In a compositional and modular analysis, a recursive function is abstracted
by its contract in the analyses of its callers. Once the function's own
analysis has proved its contract, a refinement of a caller defines the
function at the SMT level, with define-funs-rec, and the solver unfolds the
definition. The first analysis of the caller falsifies the checks, which the
contract does not give, and the documented exit code counts every analysis,
so the exit code does not tell whether the refinement proved them. This checks
the answers of the last analysis of main.
"""

import json
import subprocess
from pathlib import Path

import pytest

from conftest import common_args, kind2_bin, run_timeout

models = (
    Path(__file__).parent / "regression" / "falsifiable" / "compositional" / "modular"
)


@pytest.mark.parametrize(
    "model", ["rec_def_contract_refined.lus", "rec_def_mutual_refined.lus"]
)
def test_refinement_proves_checks(model):
    args = common_args | {"--compositional": "true", "--modular": "true"}
    arg_list = [arg for pair in args.items() for arg in pair]
    run = subprocess.run(
        [kind2_bin, "-json", *arg_list, str(models / model)],
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
    assert "falsifiable" in of_main[0].values(), of_main[0]
    assert set(of_main[-1].values()) == {"valid"}, of_main[-1]
