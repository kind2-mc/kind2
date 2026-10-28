"""The bounds obligation of an access under 'pre' is checked at the instant
the access is evaluated, whether or not 'pre' is pushed into expressions
(`--lus_push_pre`): it is not pushed into an array access or element update,
which would make it evaluated at the current instant on previous values.
"""

import json
import subprocess
from pathlib import Path

import pytest

from conftest import common_args, kind2_bin, run_timeout

models = [
    Path(__file__).parent / "regression" / "success" / f"{name}.lus"
    for name in [
        "array_bounds_pre_time_invariant_index",
        "array_bounds_pre_update",
        "array_bounds_pre_index_initialized",
    ]
]


@pytest.mark.parametrize("push_pre", ["true", "false"])
@pytest.mark.parametrize("model", models, ids=lambda m: m.stem)
def test_array_bounds_push_pre(model, push_pre):
    args = common_args | {"--lus_push_pre": push_pre}
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
    assert bounds and all(v == "valid" for v in bounds.values()), answers
