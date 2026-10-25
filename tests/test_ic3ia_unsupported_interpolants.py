"""IC3IA declines a system whose interpolation query SMTInterpol rejects.

SMTInterpol's interpolation procedure takes quantifier-free input only. Over a
formula with a quantifier whose variable is used, it answers `unsupported` to
the interpolation query, and IC3IA failed an assertion on that reply and ended
with a runtime error (issue #1842). It now declines the system with a warning
that names the property, and leaves the property unknown. The decline happens
only once a refinement needs interpolants: a quantified property that IC3IA
settles without refining is still proved.
"""

import json
import os
import shutil
from pathlib import Path

import pytest

from conftest import common_args, ic3ia_args, kind2_bin, run_kind2

itp_solver = "SMTInterpol"

# Kind 2 runs SMTInterpol as `java -jar smtinterpol.jar`, with the JAR found
# on PATH (see `Flags.Smt.locate_solver`). It never runs an `smtinterpol`
# executable, so look for the JAR itself. A JAR is not executable, so
# `shutil.which` would not find it.
smtinterpol_jar = "smtinterpol.jar"


def on_path(name):
    return any(
        (Path(d) / name).is_file()
        for d in os.environ.get("PATH", "").split(os.pathsep)
        if d
    )


smtinterpol_available = shutil.which("java") is not None and on_path(
    smtinterpol_jar
)
requires_smtinterpol = pytest.mark.skipif(
    not smtinterpol_available, reason=f"java or {smtinterpol_jar} is not on PATH"
)

# The quantified variable is used, so the quantifier reaches the interpolation
# query
needs_refinement = """
node N (y: int) returns ();
let
  assert y > 0;
  check "p" forall (j: int) (j = 0 => (true -> pre y > 0));
tel
"""

# A fact about the current state, which the initial predicates settle without
# an interpolant
needs_none = """
node N (y: int) returns ();
let
  assert y > 0;
  check "p" forall (j: int) y > 0;
tel
"""


def run(path):
    """The answers to the properties and the log messages by level of a run
    of IC3IA with SMTInterpol on `path`."""
    args = common_args | ic3ia_args | {"--smt_itp_solver": itp_solver}
    arg_list = [arg for pair in args.items() for arg in pair]
    # `run_kind2` kills the whole process tree on a timeout, including the
    # `java` child, which would otherwise keep the output pipe open
    proc = run_kind2([kind2_bin, "-json", *arg_list, str(path)])
    out = proc.stdout.decode() + proc.stderr.decode()
    objs = json.loads(proc.stdout)
    logs = {}
    for obj in objs:
        if obj.get("objectType") == "log":
            logs.setdefault(obj.get("level"), []).append(obj["value"])
    answers = {
        obj["name"]: obj["answer"]["value"]
        for obj in objs
        if obj.get("objectType") == "property"
    }
    return answers, logs, out


def no_failures(logs):
    return logs.get("error", []) == [] and logs.get("fatal", []) == []


@requires_smtinterpol
def test_declines_quantified_interpolation(tmp_path):
    path = tmp_path / "model.lus"
    path.write_text(needs_refinement)
    answers, logs, out = run(path)
    assert answers.get("p") == "unknown", out
    assert no_failures(logs), out
    assert any(
        "disabled for property p: SMTInterpol computes no interpolants over "
        "quantified formulas" in msg
        for msg in logs.get("warn", [])
    ), out


@requires_smtinterpol
def test_proves_without_refinement(tmp_path):
    path = tmp_path / "model.lus"
    path.write_text(needs_none)
    answers, logs, out = run(path)
    assert answers.get("p") == "valid", out
    assert no_failures(logs), out
