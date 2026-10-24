"""IC3IA declines a system whose interpolation query SMTInterpol rejects.

SMTInterpol's interpolation procedure takes quantifier-free input only. Over a
formula with a quantifier whose variable is used, it answers `unsupported` to
the interpolation query, and IC3IA failed an assertion on that reply and ended
with a runtime error (issue #1842). It now declines the system with a warning
and leaves the property unknown. A quantifier over a variable the formula does
not use is simplified away by the solver before it interpolates, and such a
property is still proved.
"""

import json
import shutil
import subprocess

import pytest

from conftest import common_args, ic3ia_args, kind2_bin, run_timeout

itp_solver = "SMTInterpol"
itp_binary = "smtinterpol"

# The quantified variable is used, so the quantifier reaches the interpolation
# query
quantified = """
node N (y: int) returns ();
let
  assert y > 0;
  check "p" forall (j: int) (j = 0 => (true -> pre y > 0));
tel
"""

# The quantified variable is not used, and the solver drops the quantifier
vacuous = """
node N (y: int) returns ();
let
  assert y > 0;
  check "p" forall (j: int) (true -> pre y > 0);
tel
"""


def run(path):
    args = common_args | ic3ia_args | {"--smt_itp_solver": itp_solver}
    arg_list = [arg for pair in args.items() for arg in pair]
    run = subprocess.run(
        [kind2_bin, "-json", *arg_list, str(path)],
        capture_output=True,
        text=True,
        timeout=run_timeout,
    )
    objs = json.loads(run.stdout)
    logs = {
        level: [obj["value"] for obj in objs
                if obj.get("objectType") == "log" and obj.get("level") == level]
        for level in ("warn", "error", "fatal")
    }
    answers = {
        obj["name"]: obj["answer"]["value"]
        for obj in objs
        if obj.get("objectType") == "property"
    }
    return answers, logs, run.stdout + run.stderr


@pytest.mark.skipif(
    shutil.which(itp_binary) is None, reason=f"{itp_binary} is not installed"
)
def test_declines_quantified_interpolation(tmp_path):
    path = tmp_path / "model.lus"
    path.write_text(quantified)
    answers, logs, out = run(path)
    assert answers.get("p") == "unknown", out
    assert logs["error"] == [] and logs["fatal"] == [], out
    assert any(
        "computes no interpolants over quantified formulas" in msg
        for msg in logs["warn"]
    ), out


@pytest.mark.skipif(
    shutil.which(itp_binary) is None, reason=f"{itp_binary} is not installed"
)
def test_proves_vacuous_quantifier(tmp_path):
    path = tmp_path / "model.lus"
    path.write_text(vacuous)
    answers, logs, out = run(path)
    assert answers.get("p") == "valid", out
    assert logs["error"] == [] and logs["fatal"] == [], out
