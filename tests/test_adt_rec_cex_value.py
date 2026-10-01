"""A counterexample names the recursive-ADT value that actually falsifies the
property, rather than the default value of its type.

The rest of the suite reads exit codes alone, and the schema check accepts any
well-formed value, so neither notices a counterexample whose ADT streams are
all the first constructor of their type. These cases read the witness back and
check it against the property it is supposed to falsify: a list the property
says is a `Cons` has to print as a `Cons`. The payloads are left to the solver;
only what the property forces is asserted.
"""

import json
import subprocess
from pathlib import Path

import pytest

from conftest import common_args, kind2_bin, run_timeout

falsifiable = Path(__file__).parent / "regression" / "falsifiable"


def witnesses(model):
    """The streams of the counterexample of the falsified property, by name,
    as the value each takes at the first instant."""
    arg_list = [arg for pair in common_args.items() for arg in pair]
    run = subprocess.run(
        [kind2_bin, "-json", *arg_list, str(falsifiable / model)],
        capture_output=True,
        text=True,
        timeout=run_timeout,
    )
    found = [
        obj
        for obj in json.loads(run.stdout)
        if obj.get("objectType") == "property"
        and obj["answer"]["value"] == "falsifiable"
        and "counterExample" in obj
    ]
    assert len(found) == 1, run.stdout
    return {
        stream["name"]: stream["instantValues"][0][1]
        for stream in found[0]["counterExample"][0]["streams"]
    }


def constructor(value):
    assert isinstance(value, dict), value
    return value["constructor"]


# Every model whose property is falsified only by a `Cons` list in `l`
cons_models = [
    "adt_rec_cex_value.lus",
    "adt_rec_cex_match.lus",
    "adt_rec_cex_nested.lus",
    "adt_rec_cex_two_datatypes.lus",
]


@pytest.mark.parametrize("model", cons_models)
def test_list_witness_is_a_cons(model):
    found = witnesses(model)
    assert constructor(found["l"]) == "Cons", found


def test_match_arm_agrees_with_witness():
    # `ok = (h = 0)` is false, so the `Cons` arm ran and `h` is its head
    found = witnesses("adt_rec_cex_match.lus")
    assert found["h"] != 0, found
    assert found["l"]["args"][0] == found["h"], found


def test_nested_witness_has_two_cells():
    # Only the inner `Cons` arm of the nested match gives `false`
    found = witnesses("adt_rec_cex_nested.lus")
    assert constructor(found["l"]) == "Cons", found
    assert constructor(found["l"]["args"][1]) == "Cons", found


def test_tree_witness_is_a_node():
    found = witnesses("adt_rec_cex_two_datatypes.lus")
    assert constructor(found["t"]) == "Node", found


def test_array_witness_holds_three_lists():
    # No element is `Nil`, so the array may not come back short or empty
    found = witnesses("adt_rec_cex_array.lus")
    assert len(found["a"]) == 3, found
    assert [constructor(cell) for cell in found["a"]] == ["Cons"] * 3, found
