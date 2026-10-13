"""kmoxi reports a solver it cannot use as an SMT-LIB error.

A solver that cannot be found is reported on the standard output as
(error "..."), with the exit code of a solver not found (4); one that is
found but cannot be used, such as a cvc5 whose version cannot be
determined, with the exit code of an unsupported solver (5). kmoxi used to
exit silently, since it turns logging off.
"""

import os

import pytest

from conftest import run_kmoxi_process

NOT_FOUND = 4
UNSUPPORTED = 5

model = """(set-logic QF_LIA)
(define-system main :input ((i Int)) :output ((n Int)) :local ()
  :init (= n 0) :trans (= n' (+ n (ite (> i' 0) 2 0))))
(check-system main :input ((i Int)) :output ((n Int)) :local ()
  :reachable (r (= n 4)) :query (q (r)))
"""


@pytest.fixture
def path(tmp_path):
    path = tmp_path / "model.moxi"
    path.write_text(model)
    return path


def test_no_solver(tmp_path, path):
    # Neither on the path nor in the working directory, where kmoxi looks
    # for an executable too
    empty = tmp_path / "empty"
    empty.mkdir()
    res = run_kmoxi_process(path, "--enable", "BMC",
                            env=dict(os.environ, PATH=str(empty)), cwd=empty)
    assert res.returncode == NOT_FOUND, res.stdout + res.stderr
    assert res.stdout.strip() == '(error "No SMT Solver found")', res.stdout


def test_chosen_solver_not_found(tmp_path, path):
    missing = str(tmp_path / "no-z3")
    res = run_kmoxi_process(path, "--smt_solver", "Z3", "--z3_bin", missing)
    assert res.returncode == NOT_FOUND, res.stdout + res.stderr
    assert res.stdout.strip() == f'(error "Z3 executable {missing} not found")', (
        res.stdout
    )


@pytest.mark.skipif(os.name == "nt", reason="the fake solver is a shell script")
def test_unsupported_solver(tmp_path, path):
    # A cvc5 that prints no version
    fake = tmp_path / "cvc5"
    fake.write_text("#!/bin/sh\nexit 0\n")
    fake.chmod(0o755)
    res = run_kmoxi_process(path, "--smt_solver", "cvc5", "--cvc5_bin", str(fake))
    assert res.returncode == UNSUPPORTED, res.stdout + res.stderr
    assert res.stdout.strip() == '(error "Couldn\'t determine cvc5 version")', (
        res.stdout
    )
