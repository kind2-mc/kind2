"""An all-nullary datatype is compiled to an enum, not to a record.

This is what lets `enum` be surface syntax for an all-nullary datatype, and it
is only observable from outside through the machine-readable stream metadata,
the interpreter's acceptance of a value named by its constructor, and the value
an enum-typed payload field takes in a counterexample. The rest of the suite
reads exit codes, so none of it would notice the record encoding coming back.
"""

import json
import subprocess
import xml.etree.ElementTree as ET
from pathlib import Path

from conftest import common_args, kind2_bin, run_timeout

regression = Path(__file__).parent / "regression"


def run(model, *extra):
    arg_list = [arg for pair in common_args.items() for arg in pair]
    return subprocess.run(
        [kind2_bin, *extra, *arg_list, str(regression / model)],
        capture_output=True,
        text=True,
        timeout=run_timeout,
    ).stdout


def streams_xml(model):
    results = ET.fromstring(run(model, "-xml"))
    return {s.get("name"): s for s in results.iter("Stream")}


def streams_json(model):
    found = [
        obj
        for obj in json.loads(run(model, "-json"))
        if obj.get("objectType") == "property" and "counterExample" in obj
    ]
    assert len(found) == 1
    return {s["name"]: s for s in found[0]["counterExample"][0]["streams"]}


def test_xml_stream_is_an_enum():
    """A nullary datatype's stream carries the enum metadata, naming the type
    and listing its constructors as the enum's values."""
    c = streams_xml("falsifiable/nullary_datatype_enum_stream.lus")["c"]
    assert c.get("type") == "enum"
    assert c.get("enumName") == "color"
    assert c.get("values") == "Red, Green, Blue"


def test_json_stream_is_an_enum():
    c = streams_json("falsifiable/nullary_datatype_enum_stream.lus")["c"]
    assert c["type"] == "enum"
    assert c["typeInfo"]["name"] == "color"
    assert c["typeInfo"]["values"] == ["Red", "Green", "Blue"]


def test_cex_value_is_a_constructor_name():
    c = streams_json("falsifiable/nullary_datatype_enum_stream.lus")["c"]
    assert c["instantValues"][0][1] in ("Red", "Green", "Blue")


def test_interpreter_accepts_constructor_names(tmp_path):
    """The interpreter reads an input value written as a constructor name,
    which it can only do while the type is an enum."""
    csv = tmp_path / "input.csv"
    csv.write_text("c,Red,Green,Blue\n")
    out = run(
        "falsifiable/nullary_datatype_enum_stream.lus",
        "--enable",
        "interpreter",
        "--interpreter_input_file",
        str(csv),
    )
    assert "Red" in out and "Green" in out and "Blue" in out


def test_enum_payload_value_in_cex():
    """An enum-typed payload field of a record-encoded datatype is a plain
    field, so the counterexample shows its value rather than a placeholder."""
    p = streams_json("falsifiable/adt_enum_payload_cex.lus")["p"]
    assert p["instantValues"][0][1] == "MkP(Green)"
