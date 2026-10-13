"""Reading the output of a killed run gives up on pipes held open elsewhere.

kill_tree makes a best effort: on POSIX it kills the process group of the
run, and a process that left that group survives it. Such a process keeps
the pipes of the run open, and the kmoxi tests read the output of a run they
had killed without a timeout, which waited forever for an end that never
came and stalled the whole session. kill_and_communicate bounds that read,
and keeps what it had read when it gave up.

The run here writes a line to its standard output and one to its standard
error, starts a child in a session of its own, which inherits both, and then
waits to be killed.
"""

import os
import signal
import subprocess
import sys
import time

import pytest

from conftest import kill_and_communicate

run = """
import subprocess, sys, time
print("partial answer", flush=True)
print("err line", file=sys.stderr, flush=True)
child = subprocess.Popen(
    [sys.executable, "-c", "import time; time.sleep(600)"],
    start_new_session=True,
)
with open(sys.argv[1], "w") as f:
    f.write(str(child.pid))
time.sleep(600)
"""


@pytest.mark.skipif(os.name == "nt", reason="no sessions to escape to")
def test_gives_up_on_escaped_child(tmp_path):
    pid_file = tmp_path / "child.pid"
    proc = subprocess.Popen(
        [sys.executable, "-c", run, str(pid_file)],
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        start_new_session=True,
    )
    child = None
    try:
        deadline = time.monotonic() + 30
        while not pid_file.exists() or not pid_file.read_text():
            assert time.monotonic() < deadline, "the run did not start its child"
            assert proc.poll() is None, "the run exited before starting its child"
            time.sleep(0.1)
        child = int(pid_file.read_text())
        start = time.monotonic()
        output, errors = kill_and_communicate(proc, timeout=2)
        assert time.monotonic() - start < 20
        assert proc.poll() is not None, "the run was not killed"
        assert output == b"partial answer\n"
        assert errors == b"err line\n"
    finally:
        try:
            os.killpg(proc.pid, signal.SIGKILL)
        except OSError:
            pass
        if child is not None:
            try:
                os.kill(child, signal.SIGKILL)
            except OSError:
                pass
