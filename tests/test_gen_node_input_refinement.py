"""The refinement types a generated node gives the variables it reads.

A node generated for 'any', 'choose', a type ascription, a temporal branch or
a restart takes the variables of the enclosing node as arguments. A refinement
on one of them yields an obligation at the call site, which the enclosing node
discharges with the refinement it already established. That only works while
the two agree: a predicate that calls a stateful or nondeterministic node reads
an instance of its own in the generated node, so such a predicate is dropped. The
conjuncts that do agree are kept, and are still checked.
"""

import json
import subprocess

import pytest

from conftest import common_args, kind2_bin, run_timeout

nat = "type Nat = subtype { n: int | n >= 0 };\n"

nondet = "node imported nd (z: int) returns (t: int);\n"

any_op = """
node main(x: %s) returns (y: int);
let
  y = any { u: int | u = x };
  check "p" y = x;
tel
"""

temporal_branch = """
node main(c: bool; x: %s) returns (y: int);
let
  y = when c then (x -> pre x) else 0;
  check "p" (not c) => (y = 0);
tel
"""


def properties(tmp_path, model):
    """The answer to each property of the only analysis of the model"""
    path = tmp_path / "model.lus"
    path.write_text(model)
    arg_list = [arg for pair in common_args.items() for arg in pair]
    proc = subprocess.run(
        [kind2_bin, "-json", *arg_list, str(path)],
        capture_output=True,
        text=True,
        timeout=run_timeout,
    )
    return {
        obj["name"]: obj["answer"]["value"]
        for obj in json.loads(proc.stdout)
        if obj.get("objectType") == "property"
    }


@pytest.mark.parametrize(
    "template, subtype",
    [
        (any_op, "main.any_L5C7[L5C7].SubType[L5C7]"),
        (temporal_branch, "SubType[L5C20]"),
    ],
)
def test_refinement_without_node_call_is_checked(tmp_path, template, subtype):
    model = nat + template % "Nat"
    assert properties(tmp_path, model) == {"p": "valid", subtype: "valid"}


@pytest.mark.parametrize("template", [any_op, temporal_branch])
def test_refinement_calling_a_node_is_dropped(tmp_path, template):
    model = nondet + template % "subtype { z: int | nd (z) = z }"
    assert properties(tmp_path, model) == {"p": "valid"}


@pytest.mark.parametrize(
    "template, subtype",
    [
        (any_op, "main.any_L5C7[L5C7].SubType[L5C7]"),
        (temporal_branch, "SubType[L5C20]"),
    ],
)
def test_conjunct_without_node_call_is_kept(tmp_path, template, subtype):
    model = nondet + template % "subtype { z: int | nd (z) = z and z >= 0 }"
    assert properties(tmp_path, model) == {"p": "valid", subtype: "valid"}
