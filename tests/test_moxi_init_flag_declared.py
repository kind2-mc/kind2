"""The init flag of a MoXI system is declared to the solvers.

TransSys.mk_trans_sys adds a one-state invariant that mentions the init
flag of the system, and the engines declare to their solvers exactly the
state variables of the system. The MoXI front end used to create the flag
without listing it among the state variables, so every engine that asserted
the invariant failed with an "unknown constant" solver error, and only IC3IA,
which does not, could answer. Here the query is unsatisfiable, and the
engines that used to fail must say so: BMC with k-induction, and IC3QE.

The model has a subsystem, so that the call also passes the flag of the
caller to the callee, whose init and trans predicates take it first.
"""

import subprocess

import pytest

from conftest import kmoxi_args, kmoxi_bin, run_timeout

model = """
(set-logic QF_LIA)
(define-system Counter
  :input () :output ((c Int)) :local ()
  :init (= c 0) :trans (= c' (+ c 1)) :inv true)
(define-system main
  :input () :output ((x Int)) :local ()
  :subsys (C (Counter x)))
(check-system main
  :input () :output ((x Int)) :local ()
  :reachable (rch (< x 0))
  :query (q (rch)))
"""


@pytest.mark.parametrize(
    "engines",
    [["BMC", "IND"], ["IC3QE"]],
    ids=["bmc-ind", "ic3qe"],
)
def test_query_unsat_without_solver_error(tmp_path, engines):
    if not kmoxi_bin.exists():
        pytest.skip(f"{kmoxi_bin} is not built (make kmoxi)")

    path = tmp_path / "counter.moxi"
    path.write_text(model)
    args = kmoxi_args | {"--timeout": "30"}
    arg_list = [arg for pair in args.items() for arg in pair]
    enable = [arg for engine in engines for arg in ("--enable", engine)]
    run = subprocess.run(
        [kmoxi_bin, "-v", *arg_list, *enable, str(path)],
        capture_output=True,
        text=True,
        timeout=run_timeout,
    )
    assert "SMT solver failed" not in run.stdout, run.stdout
    assert ":query (q :result unsat" in run.stdout, run.stdout
