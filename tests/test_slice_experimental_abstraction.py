"""An abstract node is replaced by its contract with experimental slicing.

With `--slice_nodes experimental`, the nodes were not sliced to the
abstraction of the analysis, so a node abstracted by its contract kept its
implementation, and the contract was asserted on top of it. When the
implementation does not satisfy the contract, the system is inconsistent and
every property holds vacuously. The property of main is falsifiable under the
abstraction of Callee, whatever the slicing mode.
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
    / "compositional"
    / "modular"
    / "slice_experimental_abstraction.lus"
)


@pytest.mark.parametrize("slicing", ["on", "off", "experimental"])
def test_abstract_node_replaced_by_contract(slicing):
    args = common_args | {
        "--compositional": "true",
        "--modular": "true",
        "--slice_nodes": slicing,
        "--timeout": "20",
    }
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

    assert of_main, run.stdout
    assert of_main[0] == {"c": "falsifiable"}
