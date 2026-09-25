"""IC3IA answers the properties of a refinement.

IC3IA builds its own system for each property it checks, sliced to the cone
of that property. In a refinement, the statuses of the previous analysis are
carried over to the new system, and that failed with PropertyNotFound for the
properties outside of the cone, which the sliced system does not have: IC3IA
never answered in the refinement. The first analysis falsifies both properties
under the contract of Sub, and the documented exit code counts every analysis,
so the exit code does not tell this apart from a correct run. This checks the
answers of the refinement.
"""

import json
import shutil
import subprocess
from pathlib import Path

import pytest

from conftest import common_args, ic3ia_args, ic3ia_solver, kind2_bin, run_timeout

model = (
    Path(__file__).parent
    / "regression"
    / "falsifiable"
    / "ic3ia"
    / "compositional"
    / "modular"
    / "ic3ia_refinement_sliced.lus"
)


@pytest.mark.skipif(
    shutil.which(ic3ia_solver) is None, reason=f"{ic3ia_solver} is not installed"
)
def test_ic3ia_answers_in_refinement():
    args = (
        common_args
        | ic3ia_args
        | {"--slice_nodes": "on", "--compositional": "true", "--modular": "true"}
    )
    arg_list = [arg for pair in args.items() for arg in pair]
    run = subprocess.run(
        [kind2_bin, "-json", *arg_list, str(model)],
        capture_output=True,
        text=True,
        timeout=run_timeout,
    )

    # The parameter of each analysis, and the answers to its properties
    analyses = []
    for obj in json.loads(run.stdout):
        if obj.get("objectType") == "analysisStart":
            analyses.append((obj["top"], {}))
        elif obj.get("objectType") == "property":
            analyses[-1][1][obj["name"]] = obj["answer"]["value"]

    # The first analysis of main falsifies both checks under Sub's contract,
    # and the refinement proves them
    of_main = [answers for top, answers in analyses if top == "main"]
    assert len(of_main) == 2, analyses
    assert {name: of_main[0].get(name) for name in ("pa", "pb")} == {
        "pa": "falsifiable",
        "pb": "falsifiable",
    }
    assert {name: of_main[1].get(name) for name in ("pa", "pb")} == {
        "pa": "valid",
        "pb": "valid",
    }
