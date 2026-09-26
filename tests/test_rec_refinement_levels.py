"""A refinement unrolls a recursive function before defining it.

In a compositional and modular analysis, a recursive function is abstracted
by its contract in the analyses of its callers. Once the function's own
analysis has proved its contract, the refinements of a caller unroll the
function once, then up to --rec_unrollings times, its recursive calls
abstracted by the contract, and stop there. Each refinement is an analysis
of the caller. The first analysis falsifies the
check, and the documented exit code counts every analysis, so this checks
the number of analyses of the caller and their answers.
"""

import json
import subprocess
from pathlib import Path

import pytest

from conftest import common_args, kind2_bin, run_timeout

models = (
    Path(__file__).parent / "regression" / "falsifiable" / "compositional" / "modular"
)


def answers_of_main(model, limit):
    args = common_args | {
        "--compositional": "true",
        "--modular": "true",
        "--rec_unrollings": str(limit),
    }
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
    return [answers["p"] if "p" in answers else list(answers.values())[0] for answers in of_main]


@pytest.mark.parametrize(
    "model, limit, expected",
    [
        # Fact(1) = 1 needs Fact(0) to be the body: two unrollings. At the
        # limit, no further refinement is tried.
        ("rec_def_contract_unrolled.lus", 1, ["falsifiable", "falsifiable"]),
        ("rec_def_contract_unrolled.lus", 2, ["falsifiable", "falsifiable", "valid"]),
        ("rec_def_contract_unrolled.lus", 3, ["falsifiable", "falsifiable", "valid"]),
        # Fact(3) = 6 needs Fact(0) to be the body: four unrollings
        ("rec_def_contract_refined.lus", 2, ["falsifiable"] * 3),
        ("rec_def_contract_refined.lus", 4, ["falsifiable"] * 4 + ["valid"]),
    ],
)
def test_analyses_of_caller(model, limit, expected):
    assert answers_of_main(model, limit) == expected
