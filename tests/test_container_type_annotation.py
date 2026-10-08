"""An empty container's type annotation prints by the declared type name.

The annotation is part of the property expression, so it is shown whenever a
property is reported. Without rewriting it back, a datatype prints as the
record it is desugared to and an enum as its inline definition, exposing the
encoding and the generated field names. Nothing else in the suite reads a
rendered property expression.
"""

import json
import subprocess
from pathlib import Path

from conftest import common_args, kind2_bin, run_timeout

model = Path(__file__).parent / "regression" / "success" / "container_type_annotation_display.lus"


def run(*extra):
    arg_list = [arg for pair in common_args.items() for arg in pair]
    return subprocess.run(
        [kind2_bin, *extra, *arg_list, str(model)],
        capture_output=True,
        text=True,
        timeout=run_timeout,
    ).stdout


def test_json_annotation_uses_declared_names():
    exprs = [
        obj["expr"]
        for obj in json.loads(run("-json"))
        if obj.get("objectType") == "property" and "expr" in obj
    ]
    assert any("set[]@<D>" in e for e in exprs), exprs
    assert any("map[]@<Color,D>" in e for e in exprs), exprs
    assert not any("_tag" in e for e in exprs), exprs


def test_text_annotation_uses_declared_names():
    out = run()
    assert "set[]@<D>" in out
    assert "map[]@<Color,D>" in out
    assert "_tag" not in out
