"""The solvers Kind 2 kills do not linger as zombie processes.

At the end of an analysis, the supervisor terminates the engines, and their
solvers are killed with SIGKILL. The killed process used to be reaped with a
single non-blocking wait right after the kill, which usually found it still
alive: it then became a zombie, holding a process slot until Kind 2 exited.
A modular run over many nodes has many analyses, and accumulated hundreds of
zombies, enough to exhaust the processes a user may have on a machine running
several Kind 2 at once.

The model is generated: 60 nodes with a property each, all called by main,
analyzed one by one in a modular run. The children of Kind 2 are sampled
while it runs, and the zombies among them counted.
"""

import subprocess
import sys
import time

import pytest

from conftest import common_args, kind2_bin, run_timeout

n = 60

model = "\n".join(
    [
        f"node n{i} (x: int) returns (y: int);\n"
        f"let\n"
        f"  y = x + {i + 1};\n"
        f"  check \"p{i}\" y > x or x < 0;\n"
        f"tel\n"
        for i in range(n)
    ]
    + [
        "node main (x: int) returns (y: int);",
        "let",
        "  y = " + " + ".join(f"n{i}(x)" for i in range(n)) + ";",
        "tel",
    ]
)


def zombie_children(pid):
    ps = subprocess.run(
        ["ps", "-A", "-o", "ppid=,stat="], capture_output=True, text=True
    )
    count = 0
    for line in ps.stdout.splitlines():
        fields = line.split()
        if len(fields) >= 2 and fields[0] == str(pid) and fields[1].startswith("Z"):
            count += 1
    return count


@pytest.mark.skipif(sys.platform == "win32", reason="no zombie processes on Windows")
def test_killed_solvers_are_reaped(tmp_path):
    path = tmp_path / "many_nodes.lus"
    path.write_text(model)
    args = common_args | {"--modular": "true"}
    arg_list = [arg for pair in args.items() for arg in pair]
    proc = subprocess.Popen(
        [kind2_bin, *arg_list, str(path)],
        stdout=subprocess.DEVNULL,
        stderr=subprocess.DEVNULL,
    )
    most = 0
    started = time.monotonic()
    try:
        while proc.poll() is None and time.monotonic() - started < run_timeout:
            most = max(most, zombie_children(proc.pid))
            time.sleep(0.1)
    finally:
        if proc.poll() is None:
            proc.kill()
        proc.wait()
    assert proc.returncode == 0
    # A handful may be caught between their death and their reaping
    assert most < 20, most
