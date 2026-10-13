"""kmoxi gives every check-system its response when time runs out.

When the time limit is reached, the engines are stopped, and the queries
not answered yet are unknown, as the MoXI language definition gives for
timeouts. kmoxi used to print nothing when an engine was still running.
"""

import subprocess

import pytest

from conftest import kill_tree, kmoxi_args, kmoxi_bin


head = """(set-logic QF_LIA)
(define-system main :input ((i Int)) :output ((n Int)) :local ()
  :init (= n 0) :trans (= n' (+ n (ite (> i' 0) 2 0))))
(check-system main :input ((i Int)) :output ((n Int)) :local ()
"""


def run(tmp_path, model, extra, env=None, timeout=60):
    if not kmoxi_bin.exists():
        pytest.skip(f"{kmoxi_bin} is not built (make kmoxi)")
    path = tmp_path / "model.moxi"
    path.write_text(model)
    args = kmoxi_args | {"--timeout": "30"}
    arg_list = [arg for pair in args.items() for arg in pair]
    proc = subprocess.Popen(
        [kmoxi_bin, *arg_list, *extra, str(path)],
        stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True,
        start_new_session=True, env=env,
    )
    try:
        stdout, stderr = proc.communicate(timeout=timeout)
    except subprocess.TimeoutExpired:
        kill_tree(proc)
        proc.communicate()
        pytest.fail(f"no answer after {timeout}s")
    return proc.returncode, stdout, stderr


def test_response_on_timeout(tmp_path):
    # n is even: BMC alone never answers
    attrs = "  :reachable (odd (= n 3)) :query (q (odd)))\n"
    _, out, err = run(tmp_path, head + attrs,
                      ["--enable", "BMC", "--timeout", "2"])
    assert out.startswith("(check-system-response"), out + err
    assert ":query (q unknown" in out, out
