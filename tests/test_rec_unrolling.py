"""A recursive function is unrolled further when a counterexample reaches a
recursive call past its unrollings.

Outside of compositional analyses, the recursive calls past the unrollings
of a function are left unconstrained. A counterexample that reaches one may
be spurious: the function is then unrolled once more and the engines run
again, up to --rec_unrollings, without an analysis of its own. A property
whose counterexample reaches such a call at the limit is left unknown, and
the run ends rather than waiting for its timeout.
"""

import json
import subprocess
import time
from pathlib import Path

import pytest

from conftest import common_args, kind2_bin, run_timeout

models = Path(__file__).parent / "regression"


def run(model, extra):
    args = common_args | {"--timeout": "60"} | extra
    arg_list = [arg for pair in args.items() for arg in pair]
    started = time.monotonic()
    proc = subprocess.run(
        [kind2_bin, "-json", *arg_list, str(models / model)],
        capture_output=True,
        text=True,
        timeout=run_timeout,
    )
    elapsed = time.monotonic() - started
    answers = {
        obj["name"]: obj["answer"]["value"]
        for obj in json.loads(proc.stdout)
        if obj.get("objectType") == "property"
    }
    return proc.returncode, answers, elapsed


# Fact(3) = 6 needs Fact(0) to be the body: four unrollings
def test_unrolled_until_the_arguments_are_exhausted():
    code, answers, _ = run("success/rec_def_contract.lus", {})
    assert code == 0, answers
    assert answers["fact3"] == "valid"


# In a modular analysis, Fact is analyzed on its own first, and its guarantee
# holds only by induction over the recursion: it is left unknown, while the
# check of main is proved as above
def test_unrolled_in_modular_analysis():
    code, answers, _ = run("success/rec_def_contract.lus", {"--modular": "true"})
    assert answers["fact3"] == "valid", answers
    assert answers["positive"] == "unknown"
    assert code == 30


def test_left_unknown_at_the_limit():
    code, answers, elapsed = run(
        "success/rec_def_contract.lus", {"--rec_unrollings": "3"}
    )
    assert answers["fact3"] == "unknown", answers
    assert code == 30
    # The run ends once every property is settled or given up on
    assert elapsed < 30, elapsed


# The guarantee of Fact holds only by induction over the recursion, which
# unrolling cannot provide: every unrolling up to the limit finds a
# counterexample that reaches the unconstrained call
def test_guarantee_needing_induction_left_unknown():
    code, answers, elapsed = run("success/compositional/factorial.lus", {})
    assert answers["fact is positive"] == "unknown", answers
    assert code == 30
    assert elapsed < 30, elapsed
