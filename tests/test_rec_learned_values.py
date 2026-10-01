"""The values of calls evaluated by the check of a spurious counterexample
are given to the refinements of the caller.

In a compositional and modular analysis, a counterexample found with a
recursive function abstracted by its contract is checked against the
function: its calls are evaluated at their concrete arguments. When the
property cannot fail with their values, the counterexample is spurious, and
the values, of a function proved terminating, are given to the refinements
of the caller as facts. A check whose argument is an input that the check
fixes, such as x = 3 => Fact(x) = 6, is then proved in the first refinement,
whatever the number of unrollings it would take, instead of after as many
refinements as the call needs unrollings. A falsifiable run counts every
analysis in its exit code, so this checks the answers of each analysis of
the top node.
"""

import json
import subprocess
from pathlib import Path

import pytest

from conftest import common_args, kind2_bin, run_timeout

models = (
    Path(__file__).parent / "regression" / "falsifiable" / "compositional" / "modular"
)


def analyses_of(model, top, extra):
    args = common_args | {"--compositional": "true", "--modular": "true"} | extra
    arg_list = [arg for pair in args.items() for arg in pair]
    run = subprocess.run(
        [kind2_bin, "-json", *arg_list, str(models / model)],
        capture_output=True,
        text=True,
        timeout=run_timeout,
    )
    of_top = []
    current = None
    for obj in json.loads(run.stdout):
        if obj.get("objectType") == "analysisStart":
            current = obj["top"]
            if current == top:
                of_top.append({})
        elif obj.get("objectType") == "property" and current == top:
            if "[" not in obj["name"]:
                of_top[-1][obj["name"]] = obj["answer"]["value"]
    return of_top


# Fact(3) = 6 needs four unrollings, IsEven(6) and IsOdd(6) seven, and the
# guarantee of reverse three appends to Nil; each is proved at the default
# limit, in the first refinement, with the values learned
@pytest.mark.parametrize(
    "model, top",
    [
        ("rec_def_contract_refined.lus", "main"),
        ("rec_def_mutual_refined.lus", "main"),
        ("rec_refinement_callee_guarantee.lus", "reverse"),
    ],
)
def test_learned_values_prove_in_first_refinement(model, top):
    of_top = analyses_of(model, top, {})
    assert len(of_top) == 2, of_top
    assert "falsifiable" in of_top[0].values(), of_top[0]
    assert set(of_top[1].values()) == {"valid"}, of_top[1]


# Without the values, the same checks need more unrollings than the default
# limit, and stay falsified
@pytest.mark.parametrize(
    "model, top",
    [
        ("rec_def_contract_refined.lus", "main"),
        ("rec_def_mutual_refined.lus", "main"),
    ],
)
def test_without_learned_values_the_limit_is_too_low(model, top):
    of_top = analyses_of(model, top, {"--rec_learn_values": "false"})
    assert "valid" not in of_top[-1].values(), of_top[-1]


# A property the function itself falsifies is not proved by the values
def test_learned_values_do_not_prove_a_false_property():
    of_main = analyses_of("rec_genuine_mixed.lus", "main", {})
    assert of_main[-1]["needs"] == "valid", of_main[-1]
    assert of_main[-1]["wrong"] == "falsifiable", of_main[-1]
