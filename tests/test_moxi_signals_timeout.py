"""kmoxi stops at its --timeout and on SIGTERM, and takes its solvers along.

kmoxi did not install the signal handlers and the wall clock timeout that
kind2 installs before an analysis. It ran past --timeout, and a SIGTERM
ended it on the spot, without the teardown that kills the solvers. The
solvers are started from engine domains, which block SIGTERM, and keep
that signal mask across exec: left behind, they ran until killed with
SIGKILL.

The query here is only reachable after 100000 steps, so that the engines
are still running when the run is stopped. The run leads a process group
of its own, which its solvers belong to: once kmoxi has stopped, nothing
may be left in that group. An idle solver exits by itself when kmoxi dies,
on the end of its input, so the SIGTERM test also requires that kmoxi
handled the signal, running its teardown, rather than being killed by it.
"""

import os
import signal
import subprocess
import time

import pytest

from conftest import kmoxi_args, kill_tree, kmoxi_bin

model = """
(set-logic QF_LIA)
(define-system main :input () :output ((x Int)) :local ()
  :init (= x 0) :trans (= x' (+ x 1)))
(check-system main :input () :output ((x Int)) :local ()
  :reachable (rch (= x 100000)) :query (q (rch)))
"""

# How long kmoxi may take to stop once it is asked to, in seconds
grace = 30


def group_alive(pgid):
    try:
        os.killpg(pgid, 0)
    except ProcessLookupError:
        return False
    return True


def start(tmp_path, extra):
    if not kmoxi_bin.exists():
        pytest.skip(f"{kmoxi_bin} is not built (make kmoxi)")
    path = tmp_path / "far.moxi"
    path.write_text(model)
    args = kmoxi_args | {"--timeout": "0"}
    arg_list = [arg for pair in args.items() for arg in pair]
    return subprocess.Popen(
        [kmoxi_bin, *arg_list, *extra, str(path)],
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        start_new_session=True,
    )


def check_stops(proc, what):
    try:
        proc.communicate(timeout=grace)
    except subprocess.TimeoutExpired:
        kill_tree(proc)
        proc.communicate()
        pytest.fail(f"kmoxi still running {grace}s after {what}")
    # The solvers are killed by the teardown; give them a moment to go
    deadline = time.monotonic() + 5
    while group_alive(proc.pid) and time.monotonic() < deadline:
        time.sleep(0.1)
    left = group_alive(proc.pid)
    if left:
        os.killpg(proc.pid, signal.SIGKILL)
    assert not left, f"processes of kmoxi left running after {what}"


@pytest.mark.skipif(os.name == "nt", reason="no process groups or SIGTERM")
def test_stops_at_timeout(tmp_path):
    proc = start(tmp_path, ["--timeout", "3"])
    check_stops(proc, "its 3s timeout")


@pytest.mark.skipif(os.name == "nt", reason="no process groups or SIGTERM")
def test_stops_on_sigterm(tmp_path):
    proc = start(tmp_path, [])
    time.sleep(3)
    assert proc.poll() is None, "kmoxi stopped before it was signalled"
    proc.send_signal(signal.SIGTERM)
    check_stops(proc, "SIGTERM")
    assert proc.returncode != -signal.SIGTERM, "kmoxi was killed by SIGTERM"
