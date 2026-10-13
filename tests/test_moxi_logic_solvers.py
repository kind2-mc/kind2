"""kmoxi picks its SMT solvers from the logic the input declares.

For the solver roles left to detection, the declared logic decides: QF_BV
uses Bitwuzla as main solver, QF_ABV and QF_LIA use Z3, and all three use
MathSAT for interpolation and Z3 for quantifier elimination. A solver given on
the command line wins, and a preferred solver that is not found is left to the
usual detection.

Each solver on the path is replaced by a shim that records its name before
running the real solver, which tells which solvers a run started. Z3 is
started for quantifier elimination in every configuration, so whether
Bitwuzla runs is what tells them apart.
"""

import os
import shutil
import subprocess

import pytest

from conftest import kmoxi_args, kill_tree, kmoxi_bin

solvers = ["z3", "bitwuzla", "mathsat"]

# A system whose query BMC settles at depth 1
models = {
    "QF_BV": "(_ BitVec 4)",
    "QF_ABV": "(_ BitVec 4)",
    "QF_LIA": "Int",
}


def model(logic):
    sort = models[logic]
    zero = "0" if sort == "Int" else "#b0000"
    one = "1" if sort == "Int" else "#b0001"
    plus = "+" if sort == "Int" else "bvadd"
    return f"""
(set-logic {logic})
(define-system main :input () :output ((x {sort})) :local ()
  :init (= x {zero}) :trans (= x' ({plus} x {one})))
(check-system main :input () :output ((x {sort})) :local ()
  :reachable (rch (= x {one})) :query (q (rch)))
"""


@pytest.fixture
def shims(tmp_path):
    missing = [s for s in solvers if shutil.which(s) is None]
    if missing:
        pytest.skip(f"not installed: {', '.join(missing)}")
    shim_dir = tmp_path / "shims"
    shim_dir.mkdir()
    log = tmp_path / "started"
    for s in solvers:
        shim = shim_dir / s
        shim.write_text(
            f'#!/bin/sh\necho {s} >> "{log}"\nexec "{shutil.which(s)}" "$@"\n'
        )
        shim.chmod(0o755)
    return shim_dir, log


def run_kmoxi(tmp_path, shims, logic, extra=()):
    if not kmoxi_bin.exists():
        pytest.skip(f"{kmoxi_bin} is not built (make kmoxi)")
    shim_dir, log = shims
    path = tmp_path / f"{logic}.moxi"
    path.write_text(model(logic))
    env = dict(os.environ, PATH=f"{shim_dir}{os.pathsep}{os.environ['PATH']}")
    args = kmoxi_args | {"--timeout": "30"}
    arg_list = [arg for pair in args.items() for arg in pair]
    proc = subprocess.Popen(
        [kmoxi_bin, *arg_list, *extra, str(path)],
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
        env=env,
        start_new_session=True,
    )
    try:
        stdout, _ = proc.communicate(timeout=60)
    except subprocess.TimeoutExpired:
        kill_tree(proc)
        proc.communicate()
        pytest.fail("no answer after 60s")
    assert ":query (q sat" in stdout, stdout
    return set(log.read_text().split()) if log.exists() else set()


@pytest.mark.skipif(os.name == "nt", reason="the shims are shell scripts")
@pytest.mark.parametrize(
    "logic, bitwuzla", [("QF_BV", True), ("QF_ABV", False), ("QF_LIA", False)]
)
def test_main_solver_from_logic(tmp_path, shims, logic, bitwuzla):
    started = run_kmoxi(tmp_path, shims, logic, ["--enable", "BMC"])
    assert ("bitwuzla" in started) == bitwuzla, started
    assert "z3" in started, started


@pytest.mark.skipif(os.name == "nt", reason="the shims are shell scripts")
def test_command_line_solver_wins(tmp_path, shims):
    started = run_kmoxi(
        tmp_path, shims, "QF_BV", ["--enable", "BMC", "--smt_solver", "z3"]
    )
    assert started == {"z3"}, started


@pytest.mark.skipif(os.name == "nt", reason="the shims are shell scripts")
def test_missing_preferred_solver_detected(tmp_path, shims):
    started = run_kmoxi(
        tmp_path,
        shims,
        "QF_BV",
        ["--enable", "BMC", "--bitwuzla_bin", str(tmp_path / "no-bitwuzla")],
    )
    assert started == {"z3"}, started
