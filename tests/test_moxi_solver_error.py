"""kmoxi reports a solver it cannot use as an SMT-LIB error.

A solver that cannot be found, or used, is reported on the standard output
as (error "..."), with the exit code of a solver not found. kmoxi used to
exit silently, since it turns logging off.
"""

import os
import subprocess

import pytest

from conftest import kill_tree, kmoxi_args, kmoxi_bin

# Exit code of a solver not found
NOT_FOUND = 4

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


def test_no_solver_is_an_smtlib_error(tmp_path):
    attrs = "  :reachable (r (= n 4)) :query (q (r)))\n"
    empty = tmp_path / "empty"
    empty.mkdir()
    code, out, err = run(tmp_path, head + attrs, ["--enable", "BMC"],
                         env=dict(os.environ, PATH=str(empty)))
    assert code == NOT_FOUND, out + err
    assert out.strip() == '(error "No SMT Solver found")', out
    # A solver the user chose
    missing = str(tmp_path / "no-z3")
    code, out, err = run(tmp_path, head + attrs,
                         ["--smt_solver", "Z3", "--z3_bin", missing])
    assert code == NOT_FOUND, out + err
    assert out.strip() == f'(error "Z3 executable {missing} not found")', out
