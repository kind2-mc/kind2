"""A recursive function is not refined for a property it falsifies itself.

In a compositional and modular analysis, a property falsified in the analysis
of a caller used to make the caller refined, making its recursive callees
concrete and unrolling them further, up to --rec_unrollings. When the
counterexample does not rely on the contracts of the functions, but is one of
the functions as they are, the refinements only find it again, and a function
such as Ackermann's took minutes to unroll. The supervisor now checks each
counterexample against the functions as they are, and the recursive functions
are only refined for a property that is unknown or whose counterexample
relies on their contracts. A falsifiable run counts every analysis in its
exit code, so this checks the answers of each analysis of main.
"""

import json
import subprocess
from pathlib import Path

from conftest import common_args, kind2_bin, run_timeout

models = (
    Path(__file__).parent / "regression" / "falsifiable" / "compositional" / "modular"
)


def analyses_of_main(model):
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
                of_main.append({"abstract": obj.get("abstract", []), "answers": {}})
        elif obj.get("objectType") == "property" and current == "main":
            of_main[-1]["answers"][obj["name"]] = obj["answer"]["value"]
    return of_main


def test_function_not_refined_for_its_own_counterexample():
    of_main = analyses_of_main("rec_genuine_no_refinement.lus")
    assert len(of_main) == 1, of_main
    answers = of_main[0]["answers"]
    assert answers["fact"] == "falsifiable", answers
    assert answers["ack"] == "falsifiable", answers


def test_function_refined_for_another_property():
    of_main = analyses_of_main("rec_genuine_mixed.lus")
    assert len(of_main) > 1, of_main
    assert of_main[-1]["answers"]["needs"] == "valid", of_main[-1]
    assert of_main[-1]["answers"]["wrong"] == "falsifiable", of_main[-1]


def test_other_callee_refined():
    of_main = analyses_of_main("rec_genuine_other_callee.lus")
    assert len(of_main) == 2, of_main
    assert of_main[-1]["answers"]["c"] == "valid", of_main[-1]
    assert "Fact" in of_main[-1]["abstract"], of_main[-1]
