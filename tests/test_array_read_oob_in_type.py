"""Reads of enumerated values out of the bounds of arrays denote values of the type.

The model reads out of the bounds of its arrays on purpose (see #1727), so
the proof obligations of the array accesses (`ArrayBounds[...]`) are
falsified, and the model is in the falsifiable regression tree. This checks
that every other property of the model holds, under both array encodings.
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
    / "array_read_oob_in_type.lus"
)

checks = [
    "out of bounds", "in bounds", "2d", "same index", "record field", "update",
    "map in array", "array in map", "comprehension", "comprehension 2d outer",
    "comprehension 2d inner", "roundtrip", "injective",
]


@pytest.mark.parametrize("inline", ["true", "false"])
def test_array_read_oob_in_type(inline):
    args = common_args | {"--inline_arrays": inline}
    arg_list = [arg for pair in args.items() for arg in pair]
    proc = subprocess.run(
        [kind2_bin, "-json", *arg_list, str(model)],
        capture_output=True,
        text=True,
        timeout=run_timeout,
    )
    answers = {
        obj["name"]: obj["answer"]["value"]
        for obj in json.loads(proc.stdout)
        if obj.get("objectType") == "property"
    }
    bounds = {
        name: value for name, value in answers.items()
        if name.startswith("ArrayBounds[")
    }
    # Every read of the model may be out of bounds
    assert bounds and all(v == "falsifiable" for v in bounds.values()), answers
    others = {
        name: value for name, value in answers.items() if name not in bounds
    }
    assert all(v == "valid" for v in others.values()), answers
    assert set(checks) <= set(others), answers
