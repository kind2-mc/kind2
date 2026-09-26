"""The JSON output has to keep matching the schema that describes it.

`schemas/kind2-output.json` is what a consumer writes its reader against, so
it drifting away from what Kind 2 actually prints is a bug in one of the two.
Nothing noticed the drift until it was looked for: the exit code of a run
says nothing about its output, and `test_output_formats.py` only asks whether
the output parses at all, not whether it says what it is supposed to say.

Every run of the regression tree prints JSON, and `conftest.py` checks it
against the schema with `violations_in_output`, rather than a curated few
models being run for it, because drift arrives with whatever feature is added
next, and a curated list would not have it.
"""

import json
from functools import cache
from pathlib import Path

schema_path = Path(__file__).parent.parent / "schemas" / "kind2-output.json"


def jsonschema_available():
    try:
        import jsonschema  # noqa: F401
    except ImportError:
        return False
    return True


@cache
def validators():
    schema = json.loads(schema_path.read_text())
    return validators_by_object_type(schema)


def validators_by_object_type(schema):
    """A validator per definition, keyed by the `objectType` it describes.

    Every `$ref` in the schema points within it, so carrying `definitions`
    along on each one is enough to resolve them, and no resolver is needed.
    """
    from jsonschema import Draft7Validator

    definitions = schema["definitions"]
    return {
        object_type: [
            Draft7Validator({**definitions[name], "definitions": definitions})
            for name in names
        ]
        for object_type, names in definitions_by_object_type(schema).items()
    }


def definitions_by_object_type(schema):
    """The definitions that could describe an object, by its `objectType`.

    Validating against the whole `results` union reports why the object did
    not match every other member of it as well, which buries the one failure
    that matters. `objectType` says which members to try; more than one can
    carry the same one, and the closest fit is the one worth reporting.
    """
    by_type = {}
    for name, definition in schema["definitions"].items():
        object_type = definition.get("properties", {}).get("objectType", {})
        if "const" in object_type:
            by_type.setdefault(object_type["const"], []).append(name)
    return by_type


def violations_in(item, validators):
    object_type = item.get("objectType")
    if object_type not in validators:
        return [f"objectType {object_type!r} has no definition in the schema"]

    best = None
    for validator in validators[object_type]:
        found = []
        for error in validator.iter_errors(item):
            # A failed `anyOf` carries the reason for each member in its
            # context; those are what name the offending value.
            for leaf in error.context or [error]:
                where = "/".join(str(p) for p in leaf.absolute_path) or "(root)"
                found.append(f"{where}: {leaf.message}")
        if best is None or len(found) < len(best):
            best = found
    return best


# How much of the output to show on either side of where it stops parsing
parse_error_context = 400


def violations_in_output(output: str):
    """What is wrong with the JSON output of a run, as a list of lines: that
    it does not parse, or where it does not match the schema.

    Output that does not parse comes with the text around the place it stops
    parsing, which is what tells a gap in the printer from something else
    written into the middle of the output."""
    try:
        objects = json.loads(output)
    except json.JSONDecodeError as error:
        start = max(0, error.pos - parse_error_context)
        end = error.pos + parse_error_context
        return [
            f"output does not parse: {error}",
            f"output around character {error.pos}:",
            output[start:error.pos] + "<<<HERE>>>" + output[error.pos:end],
        ]
    return [
        problem
        for item in objects
        for problem in violations_in(item, validators())
    ]
