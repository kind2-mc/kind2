"""The JSON output has to keep matching the schema that describes it.

`schemas/kind2-output.json` is what a consumer writes its reader against, so
it drifting away from what Kind 2 actually prints is a bug in one of the two.
Nothing noticed the drift until it was looked for: the rest of the suite
reads exit codes, and `test_output_formats.py` only asks whether the output
parses at all, not whether it says what it is supposed to say.

Every model in the regression tree is run and validated, rather than a
curated few, because drift arrives with whatever feature is added next, and a
curated list would not have it.
"""

import json
import subprocess
from collections import Counter
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

import pytest

from conftest import common_args, kind2_bin, regression_dir, run_timeout

schema_path = Path(__file__).parent.parent / "schemas" / "kind2-output.json"

# How many models to run at once. The models are small and the time goes on
# waiting for the solver, so this is well worth doing in parallel.
workers = 8


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


def without_indices(problem):
    where, _, message = problem.partition(": ")
    kept = [step for step in where.split("/") if not step.isdigit()]
    return "/".join(kept) + ": " + message


def json_output_of(model):
    args = dict(common_args)
    if "error" in model.relative_to(regression_dir).parts:
        args["--lus_strict"] = "true"
    arg_list = [arg for pair in args.items() for arg in pair]
    run = subprocess.run(
        [kind2_bin, "-json", *arg_list, str(model)],
        capture_output=True,
        text=True,
        timeout=run_timeout,
    )
    return run.stdout


def test_json_output_matches_the_schema():
    pytest.importorskip(
        "jsonschema", reason="jsonschema is needed to check the output schema"
    )
    schema = json.loads(schema_path.read_text())
    validators = validators_by_object_type(schema)
    models = sorted(regression_dir.rglob("*.lus"))
    assert models, f"no models found under {regression_dir}"

    def check(model):
        output = json_output_of(model)
        try:
            objects = json.loads(output)
        except ValueError as error:
            return [f"{model.name}: output does not parse: {error}"]
        return [
            f"{model.name}: {problem}"
            for item in objects
            for problem in violations_in(item, validators)
        ]

    with ThreadPoolExecutor(max_workers=workers) as pool:
        found = [problem for problems in pool.map(check, models) for problem in problems]

    # One line per distinct complaint, rather than one per model: a single
    # gap in the schema is thousands of these. The index of the stream or the
    # step a value sits at says nothing about which gap it is, so it comes
    # out of the path before they are counted.
    distinct = Counter(
        without_indices(problem.split(": ", 1)[1]) for problem in found
    )
    assert not found, "\n".join(
        [f"{len(found)} schema violations over {len(models)} models,"
         f" of {len(distinct)} kinds, commonest first:"]
        + [f"  {count:6d}  {problem}" for problem, count in distinct.most_common(20)]
        + (["  ..."] if len(distinct) > 20 else [])
    )
