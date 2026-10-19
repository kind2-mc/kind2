"""The engine whose solvers take the memory of the analysis is stopped.

Kind 2 runs its solvers in processes of their own, and BMC adds to its
solver at every step without giving the memory back. Under a memory limit
on Kind 2 and its solvers, as a cgroup sets it, the first process that
exceeds the limit used to end the analysis, and with it the answers the
other engines could still give. Past 80% of the limit (that of
--memory_limit, or else of the cgroup of the process), the engine whose
solvers use the most memory is now stopped, and the others go on.

The model is a loop of Euclid's algorithm on 32-bit vectors, with a
counter that goes back to 0 after 1000, and the property that the counter
never reaches 2000. It holds, but k-induction would need some 1000 steps
to prove it, and BMC can unroll the model forever: the remainders it adds
at every step make its solver grow by megabytes per step.
"""

import sys

import pytest

from conftest import run_kmoxi, run_kmoxi_process, query_answer

gcd = """(set-logic QF_BV)
(define-system main :input ((i (_ BitVec 32)) (j (_ BitVec 32)))
  :output ((a (_ BitVec 32)) (b (_ BitVec 32)) (n (_ BitVec 32))) :local ()
  :init (and (= a (bvor i #x00000001)) (= b j) (= n #x00000000))
  :trans (and (= a' (ite (= b #x00000000) a b))
              (= b' (ite (= b #x00000000) b (bvurem a b)))
              (= n' (ite (= n #x000003e8) #x00000000 (bvadd n #x00000001)))))
(check-system main :input ((i (_ BitVec 32)) (j (_ BitVec 32)))
  :output ((a (_ BitVec 32)) (b (_ BitVec 32)) (n (_ BitVec 32))) :local ()
  :reachable (r (= n #x000007d0)) :query (q (r)))
"""


@pytest.mark.skipif(not sys.platform.startswith("linux"),
                    reason="the memory of the solvers is read from /proc")
def test_bmc_stopped_at_the_limit(tmp_path):
    path = tmp_path / "gcd.moxi"
    path.write_text(gcd)
    out, err = run_kmoxi(path, "--smt_solver", "Z3", "--enable", "BMC",
                         "--memory_limit", "500", "-v", timeout=60)
    text = out + err
    assert "Stopping bounded model checking: its solvers use" in text, text
    # The analysis goes on to its response, without an answer for q: an
    # unknown answer has no other attribute
    assert ":query (q :result unknown)" in text, text


@pytest.mark.skipif(not sys.platform.startswith("linux"),
                    reason="the memory of the solvers is read from /proc")
def test_dependents_of_a_stopped_engine_stop(tmp_path):
    # k-induction needs BMC: without it, it cannot conclude, and it is
    # stopped too, so that the analysis ends instead of running until
    # its timeout
    path = tmp_path / "gcd.moxi"
    path.write_text(gcd)
    res = run_kmoxi_process(
        path, "--smt_solver", "Z3", "--enable", "BMC", "--enable", "IND",
        "--memory_limit", "500", "-v", timeout=60)
    text = res.stdout + res.stderr
    assert "Stopping bounded model checking: its solvers use" in text, text
    assert "Terminating useless inductive step" in text, text
    assert query_answer(text) == "unknown", text
    assert "Wallclock timeout" not in text, text


def test_negative_limit_rejected(tmp_path):
    path = tmp_path / "gcd.moxi"
    path.write_text(gcd)
    res = run_kmoxi_process(path, "--memory_limit", "-1")
    assert res.returncode != 0
    assert "--memory_limit expects a non-negative integer" in (
        res.stdout + res.stderr), res.stdout + res.stderr
