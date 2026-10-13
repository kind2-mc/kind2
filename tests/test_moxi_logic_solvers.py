"""kmoxi prefers Bitwuzla as main SMT solver for a model in QF_BV.

kmoxi checks and detects its SMT solvers once the model is parsed, and takes
the logic from the set-logic command the parser read: a quoted logic name, a
set-logic in a comment and a model read from standard input are what the
parser makes of them. For QF_BV, Bitwuzla is the main solver if the user left
it to detection and it is found; otherwise, and for the other logics, the
solvers are detected as in kind2. A solver given on the command line wins.
Parsing only (--only_parse) needs no solver.

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


def model(logic, set_logic=None):
    sort = models[logic]
    zero = "0" if sort == "Int" else "#b0000"
    one = "1" if sort == "Int" else "#b0001"
    plus = "+" if sort == "Int" else "bvadd"
    if set_logic is None:
        set_logic = f"(set-logic {logic})"
    return f"""
{set_logic}
(define-system main :input () :output ((x {sort})) :local ()
  :init (= x {zero}) :trans (= x' ({plus} x {one})) :inv true;(set-logic QF_BV)
)
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


def run_kmoxi(tmp_path, shims, logic, extra=(), set_logic=None, stdin=False):
    if not kmoxi_bin.exists():
        pytest.skip(f"{kmoxi_bin} is not built (make kmoxi)")
    shim_dir, log = shims
    text = model(logic, set_logic)
    path = tmp_path / f"{logic}.moxi"
    path.write_text(text)
    env = dict(os.environ, PATH=f"{shim_dir}{os.pathsep}{os.environ['PATH']}")
    args = kmoxi_args | {"--timeout": "30"}
    arg_list = [arg for pair in args.items() for arg in pair]
    proc = subprocess.Popen(
        [kmoxi_bin, *arg_list, *extra, *([] if stdin else [str(path)])],
        stdin=subprocess.PIPE,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
        env=env,
        start_new_session=True,
    )
    try:
        stdout, _ = proc.communicate(text if stdin else "", timeout=60)
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


# The logic as the parser reads it: quoted, absent with a set-logic in a
# comment only, and from standard input
@pytest.mark.skipif(os.name == "nt", reason="the shims are shell scripts")
@pytest.mark.parametrize(
    "set_logic, stdin, bitwuzla",
    [("(set-logic |QF_BV|)", False, True), ("", False, False),
     (None, True, True)],
    ids=["quoted", "comment", "stdin"],
)
def test_logic_from_parser(tmp_path, shims, set_logic, stdin, bitwuzla):
    started = run_kmoxi(
        tmp_path, shims, "QF_BV", ["--enable", "BMC"], set_logic, stdin
    )
    assert ("bitwuzla" in started) == bitwuzla, started


def test_only_parse_needs_no_solver(tmp_path):
    if not kmoxi_bin.exists():
        pytest.skip(f"{kmoxi_bin} is not built (make kmoxi)")
    path = tmp_path / "QF_BV.moxi"
    path.write_text(model("QF_BV"))
    empty = tmp_path / "empty"
    empty.mkdir()
    res = subprocess.run(
        [kmoxi_bin, "--only_parse", "true", str(path)],
        capture_output=True, text=True, timeout=60,
        env=dict(os.environ, PATH=str(empty)),
    )
    assert res.returncode == 0, res.stdout + res.stderr
    # Analyzing does need one: kmoxi exits with the code for a solver not found
    res = subprocess.run(
        [kmoxi_bin, "--enable", "BMC", str(path)],
        capture_output=True, text=True, timeout=60,
        env=dict(os.environ, PATH=str(empty)),
    )
    assert res.returncode == 4, res.stdout + res.stderr
