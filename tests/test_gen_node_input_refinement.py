"""The refinement types a generated node gives the variables it reads.

A node generated for 'any', 'choose', a type ascription, a temporal branch or
a restart takes the variables of the enclosing node as arguments, and declares
them with their base types. A refinement is established where the value is
defined; checking it again in the generated node would evaluate its predicate
in instances of the callees of its own, which the ones of the enclosing node
need not agree with. The constraint is dropped whatever the predicate says, so
that one rule covers every refinement rather than one rule per kind of
predicate.
"""

import json
import subprocess

import pytest

from conftest import common_args, kind2_bin, run_timeout

nondet = "node imported nd (z: int) returns (t: int);\n"

deterministic = "function imported f (z: int) returns (t: int);\n"

named = "type Nat = subtype { n: int | n >= 0 };\n"

# What the refinement of the input x is written as, and what declaring it takes
refinements = {
    "node call": (nondet, "subtype { z: int | nd (z) = z }"),
    "function call": (deterministic, "subtype { z: int | f (z) = z }"),
    "arithmetic": ("", "subtype { z: int | z >= 0 }"),
    "mixed": (nondet, "subtype { z: int | nd (z) = z and z >= 0 }"),
    "named": (named, "Nat"),
}

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

templates = [any_op, temporal_branch]

template_ids = ["any", "when"]


def model(template, refinement):
    declarations, ty = refinements[refinement]
    return declarations + template % ty


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


@pytest.mark.parametrize("template", templates, ids=template_ids)
@pytest.mark.parametrize("refinement", list(refinements))
def test_input_of_a_generated_node_carries_no_obligation(
    tmp_path, template, refinement
):
    assert properties(tmp_path, model(template, refinement)) == {"p": "valid"}


@pytest.mark.parametrize("template", templates, ids=template_ids)
def test_the_predicate_does_not_change_what_is_checked(tmp_path, template):
    answers = {
        refinement: properties(tmp_path, model(template, refinement))
        for refinement in refinements
    }
    assert all(a == answers["node call"] for a in answers.values()), answers
