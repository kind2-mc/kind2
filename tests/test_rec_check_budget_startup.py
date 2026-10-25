"""The checks of the counterexamples of a round take from a budget of time
that does not count the time it takes to start their solvers.

A counterexample that reaches a recursive call past the unrollings is checked
against the functions as they are (see RecUnrolling), and the checks of a
round may take a few seconds in all. The time counted included that of
starting the solver of the queries and the one of the evaluations, which is
many times longer where starting a process is slow, as on the Windows
runners of the CI. The check of the first counterexample of the round, here a
spurious one to InvProp, then took the budget, and the counterexample to the
obligation of G one level down the recursion, which came after it and is
genuine, was left unchecked: with F at the limit of its unrollings, the
obligation was left unknown, and the run, which falsifies it otherwise, ended
unknown.

A wrapper stands in for a slow machine: it waits 3 seconds before starting
Z3, so that starting the two solvers of the round takes more than the budget.
"""

import shutil
import subprocess
import sys
from pathlib import Path

import pytest

from conftest import code_to_expected, common_args, kind2_bin, run_timeout

model = (
    Path(__file__).parent
    / "regression"
    / "falsifiable"
    / "rec_function_record_field_checked_in_recursion.lus"
)

z3 = shutil.which("z3")


@pytest.mark.skipif(z3 is None, reason="needs z3")
@pytest.mark.skipif(
    sys.platform == "win32", reason="needs a POSIX shell to slow Z3 down"
)
def test_genuine_counterexample_checked_after_slow_start(tmp_path):
    wrapper = tmp_path / "z3"
    wrapper.write_text(f'#!/bin/sh\nsleep 3\nexec "{z3}" "$@"\n')
    wrapper.chmod(0o755)
    args = common_args | {"--timeout": "60"}
    arg_list = [arg for pair in args.items() for arg in pair]
    run = subprocess.run(
        [
            kind2_bin,
            *arg_list,
            "--smt_solver", "Z3",
            "--z3_bin", str(wrapper),
            "--enable", "BMC",
            "--enable", "IND",
            str(model),
        ],
        capture_output=True,
        text=True,
        timeout=run_timeout,
    )
    assert code_to_expected.get(run.returncode) == "falsifiable", run.stdout
    assert "F[L5C34].G[L5C49].SubType[L2C47]: invalid" in run.stdout, run.stdout
