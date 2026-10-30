"""A closed output does not keep Kind 2 from killing its solvers on exit.

Whoever reads the output of Kind 2 may close it before the run is over:
the Java API does when it stops a run, right after sending SIGTERM. With
SIGPIPE ignored, every write to the output then raises Sys_error, and the
exit path writes before it kills the solvers. The first write used to
escape, then the report of it failed in the same way, and Kind 2 died of
an uncaught exception (exit code 2) with its solvers still running.

The model has a property that fails only at step 1000000, so that every
engine is busy with its solvers when the run is stopped, by SIGTERM or by
its wall clock timeout. The output is closed once the solvers are up.
"""

import os
import signal
import subprocess
import sys
import time

import pytest

from conftest import kill_tree, kind2_bin

model = """
node main () returns (c: int);
let
  c = 0 -> pre c + 1;
  check c < 1000000;
tel
"""


def child_pids(pid):
    if os.name == "nt":
        out = subprocess.run(
            ["powershell", "-NoProfile", "-Command",
             f"Get-CimInstance Win32_Process -Filter 'ParentProcessId={pid}'"
             " | ForEach-Object { $_.ProcessId }"],
            capture_output=True, text=True, timeout=60,
        ).stdout
        return {int(p) for p in out.split()}
    out = subprocess.run(
        ["ps", "-A", "-o", "pid=,ppid="], capture_output=True, text=True
    ).stdout
    return {int(f[0]) for f in map(str.split, out.splitlines())
            if len(f) == 2 and f[1] == str(pid)}


def alive(pid):
    if os.name == "nt":
        out = subprocess.run(
            ["tasklist", "/FI", f"PID eq {pid}", "/NH"],
            capture_output=True, text=True, timeout=60,
        ).stdout
        return str(pid) in out.split()
    try:
        os.kill(pid, 0)
    except ProcessLookupError:
        return False
    except PermissionError:
        return True
    # A zombie is dead, it only waits for init to reap it
    stat = subprocess.run(
        ["ps", "-o", "stat=", "-p", str(pid)], capture_output=True, text=True
    ).stdout.strip()
    return stat != "" and not stat.startswith("Z")


stops = [
    pytest.param("timeout", id="timeout"),
    pytest.param(
        "sigterm", id="sigterm",
        marks=pytest.mark.skipif(sys.platform == "win32",
                                 reason="SIGTERM kills the process on Windows"),
    ),
]


# The analysis, with engines of their own, and the interpreter, which runs
# in the main process and exits through a path of its own. The interpreter
# writes the timeout or the interruption first, in plain text through the
# standard formatter rather than the formatter of the log.
modes = [
    pytest.param([], id="analysis"),
    pytest.param(["--enable", "interpreter", "--interpreter_steps", "2000000"],
                 id="interpreter"),
]


@pytest.mark.parametrize("output", [[], ["-json"]], ids=["text", "json"])
@pytest.mark.parametrize("stop", stops)
@pytest.mark.parametrize("mode", modes)
def test_solvers_killed_with_output_closed(tmp_path, mode, stop, output):
    path = tmp_path / "late_cex.lus"
    path.write_text(model)
    timeout = "8" if stop == "timeout" else "120"
    proc = subprocess.Popen(
        [kind2_bin, "--color", "false", "--timeout", timeout, *mode, *output,
         str(path)],
        stdout=subprocess.PIPE,
        stderr=subprocess.DEVNULL,
    )
    # The interpreter runs a single solver
    started = 1 if mode else 2
    solvers = set()
    try:
        # Wait for the engines to start their solvers
        deadline = time.monotonic() + 60
        while len(solvers) < started and time.monotonic() < deadline:
            assert proc.poll() is None, "Kind 2 exited before the test stopped it"
            solvers |= child_pids(proc.pid)
            time.sleep(0.2)
        assert solvers, "Kind 2 started no solvers"

        proc.stdout.close()
        if stop == "sigterm":
            proc.send_signal(signal.SIGTERM)
        proc.wait(timeout=60)

        # The exit code the run has with its output still read: on a
        # timeout, the analysis is incomplete (the interpreter just stops),
        # and on SIGTERM it is 128 + OCaml's number for it, -11. Anything
        # else means the exit was cut short, by an uncaught exception (2)
        # or by the catch-all of main (1), and the solvers were not killed:
        # they only go away because their input reaches its end once
        # Kind 2 is gone, which the check below cannot tell from being
        # killed.
        if stop == "sigterm":
            expected = 117
        else:
            expected = 0 if mode else 30
        assert proc.returncode == expected, (
            f"exit code {proc.returncode}, expected {expected}: "
            "the exit was cut short by the closed output")

        # The solvers are killed before Kind 2 exits, but may take a moment
        # to be gone
        deadline = time.monotonic() + 10
        while time.monotonic() < deadline:
            left = {pid for pid in solvers if alive(pid)}
            if not left:
                break
            time.sleep(0.2)
        assert not left, f"solvers left running: {sorted(left)}"
    finally:
        if proc.poll() is None:
            kill_tree(proc)
        for pid in solvers:
            if alive(pid):
                try:
                    if os.name == "nt":
                        subprocess.run(["taskkill", "/F", "/PID", str(pid)],
                                       capture_output=True, timeout=60)
                    else:
                        os.kill(pid, signal.SIGKILL)
                except (OSError, subprocess.SubprocessError):
                    pass
