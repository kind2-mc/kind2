"""The machine-readable output formats have to stay machine-readable.

The rest of the suite reads exit codes alone, so nothing in it notices
`--json` or `--xml` output that no consumer can parse. These cases pin down
the shapes that have broken it: a name or an expression holding a character
the format gives a meaning to, a value with no literal of its own, and a
list whose separators have to look past the entries that print nothing.
"""

import json
import subprocess
import xml.etree.ElementTree as ET
from pathlib import Path

import pytest

from conftest import common_args, kind2_bin, run_timeout

models_dir = Path(__file__).parent / "regression"

# Models whose output has, at one time or another, not been parseable
models = [
    # A property expression that pretty-prints over more than one line
    "success/output_multiline_expr.lus",
    # Property names holding quotes, backslashes and angle brackets
    "success/output_escaped_names.lus",
    # An uninterpreted sort: neither its name nor its values are JSON literals
    "falsifiable/abstract_type.lus",
    # A constructor taking no fields, which is a constant, not an application
    "falsifiable/adt_selector_nested.lus",
    # An empty set, and a subnode printing nothing after one that printed
    "falsifiable/gen_call_in_type_decl.lus",
    # Monomorphized node names, which carry their type arguments in <>
    "success/poly_bug2.lus",
]

# The names `output_escaped_names.lus` gives its properties. Escaping has to
# carry them out and back unchanged, rather than rewrite them.
escaped_names = {
    'a "quoted" name',
    "a back\\slash name",
    "angle <brackets> & amp",
}


def output_of(model, log_format):
    arg_list = [arg for pair in common_args.items() for arg in pair]
    run = subprocess.run(
        [kind2_bin, log_format, *arg_list, str(models_dir / model)],
        capture_output=True,
        text=True,
        timeout=run_timeout,
    )
    return run.stdout


@pytest.mark.parametrize("model", models)
def test_json_output_parses(model):
    json.loads(output_of(model, "-json"))


@pytest.mark.parametrize("model", models)
def test_xml_output_parses(model):
    ET.fromstring(output_of(model, "-xml"))


def test_property_names_survive_json():
    names = {
        obj["name"]
        for obj in json.loads(output_of("success/output_escaped_names.lus", "-json"))
        if obj.get("objectType") == "property"
    }
    assert escaped_names <= names


def test_property_names_survive_xml():
    results = ET.fromstring(output_of("success/output_escaped_names.lus", "-xml"))
    names = {prop.get("name") for prop in results.iter("Property")}
    assert escaped_names <= names
