"""The nodes generated for the temporal branches of lazy constructs.

A temporal operand of a lazy construct is abstracted into a call to a
generated node, which is only activated where the condition of the construct
holds. Its properties, such as the checks of its selectors, may only hold
under that condition. A modular analysis used to analyze the generated node
on its own, without the condition, and reported its properties falsified. It
now checks them in the calling node only, where the condition is known, under
their names in the generated node, without the name of the node, and does
not analyze the generated node on its own. A property of the generated node
that fails under the condition is still reported falsified.
"""

import json
import subprocess

import pytest

from conftest import common_args, kind2_bin, run_timeout

datatype = "datatype O = N | S (v: int);\n"

implication = datatype + """
node main(x: O) returns ();
let
  check S?(x) ==> (true -> x.v = x.v);
tel
"""

when_branch = datatype + """
node main(x: O) returns (y: int);
let
  y = when S?(x) then (0 -> pre x.v) else 0;
tel
"""

# The condition does not imply that the selector is defined
wrong_guard = datatype + """
node main(x: O) returns ();
let
  check N?(x) ==> (true -> x.v = x.v);
tel
"""

# A generated node in a node called by main
nested = datatype + """
node sub(x: O) returns (y: int);
let
  y = when S?(x) then (0 -> pre x.v) else 0;
tel

node main(x: O) returns (z: int);
let
  z = sub(x);
  check S?(x) or z = 0;
tel
"""


def run_modular(tmp_path, model, modular="true"):
    """The tops of the analyses, in order, and the answers to the properties
    of each analysis"""
    path = tmp_path / "model.lus"
    path.write_text(model)
    args = common_args | {"--modular": modular, "--slice_nodes": "off"}
    arg_list = [arg for pair in args.items() for arg in pair]
    proc = subprocess.run(
        [kind2_bin, "-json", *arg_list, str(path)],
        capture_output=True,
        text=True,
        timeout=run_timeout,
    )
    analyses = []
    for obj in json.loads(proc.stdout):
        if obj.get("objectType") == "analysisStart":
            analyses.append((obj["top"], {}))
        elif obj.get("objectType") == "property":
            analyses[-1][1][obj["name"]] = obj["answer"]["value"]
    return analyses


def selectors(answers):
    return {n: v for n, v in answers.items() if "Selector" in n}


@pytest.mark.parametrize(
    "model, names",
    [
        (implication, ["Selector[L5C29]", "Selector[L5C35]"]),
        (when_branch, ["Selector[L5C34]"]),
    ],
)
def test_generated_node_checked_in_caller(tmp_path, model, names):
    analyses = run_modular(tmp_path, model)
    assert [top for top, _ in analyses] == ["main"], analyses
    assert selectors(analyses[0][1]) == dict.fromkeys(names, "valid"), analyses


def test_generated_node_not_named_in_monolithic_analysis(tmp_path):
    analyses = run_modular(tmp_path, implication, modular="false")
    assert [top for top, _ in analyses] == ["main"], analyses
    assert selectors(analyses[0][1]) == dict.fromkeys(
        ["Selector[L5C29]", "Selector[L5C35]"], "valid"
    ), analyses


def test_generated_node_falsified_in_caller(tmp_path):
    analyses = run_modular(tmp_path, wrong_guard)
    assert [top for top, _ in analyses] == ["main"], analyses
    assert selectors(analyses[0][1]) == dict.fromkeys(
        ["Selector[L5C29]", "Selector[L5C35]"], "falsifiable"
    ), analyses


def test_generated_node_of_callee(tmp_path):
    analyses = run_modular(tmp_path, nested)
    assert [top for top, _ in analyses] == ["sub", "main"], analyses
    assert selectors(analyses[0][1]) == {"Selector[L5C34]": "valid"}, analyses
    # The properties of sub are checked in the analysis of sub only
    assert selectors(analyses[1][1]) == {}, analyses
