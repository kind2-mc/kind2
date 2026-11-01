"""Calls to functions whose contracts have temporal operators.

A recursive call of such a function in a branch of a when block is clocked by
the branch, as a node call is, although the contract is compiled after the
call. The default analysis used to falsify the temporal guarantee of the
recursive instance, through an output of the instance at an instant the
branch was not taken; it now leaves it unknown, as the stateless guarantee,
since counterexamples reach the unconstrained recursive call.

The contract of an imported function may be realizable by a node only, and
then its calls may make the properties of the callers hold vacuously. Without
the contract checker, Kind 2 notes that it does not check whether a function
realizes the contract.
"""

import json
import subprocess
from pathlib import Path

from conftest import common_args, kind2_bin, run_timeout

regression = Path(__file__).parent / "regression"


def run_json(model, extra_args=None):
    args = common_args | (extra_args or {})
    arg_list = [arg for pair in args.items() for arg in pair]
    run = subprocess.run(
        [kind2_bin, "-json", *arg_list, str(model)],
        capture_output=True,
        text=True,
        timeout=run_timeout,
    )
    return run, json.loads(run.stdout)


def test_recursive_call_clocked():
    model = (
        regression
        / "success"
        / "compositional"
        / "modular"
        / "function_rec_temporal_contract.lus"
    )
    run, objs = run_json(model)
    guarantees = [
        obj
        for obj in objs
        if obj.get("objectType") == "property" and "guarantee" in obj.get("name", "")
    ]
    assert guarantees, run.stdout
    assert all(obj["answer"]["value"] != "falsifiable" for obj in guarantees), run.stdout


def test_note_on_temporal_imported_function_contract():
    model = (
        regression
        / "falsifiable"
        / "contractck"
        / "function_congruence_previous_input.lus"
    )
    run, objs = run_json(model, {"--slice_nodes": "off"})
    notes = [
        obj["value"]
        for obj in objs
        if obj.get("objectType") == "log" and obj.get("level") == "note"
    ]
    assert any(
        "imported function G" in note and "--enable CONTRACTCK" in note
        for note in notes
    ), run.stdout
