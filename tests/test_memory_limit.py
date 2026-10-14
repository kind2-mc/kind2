"""The engine whose solvers take the memory of the analysis is stopped.

Kind 2 runs its solvers in processes of their own, and BMC adds to its
solver at every step without giving the memory back. Under a memory limit
on Kind 2 and its solvers, as a cgroup sets it, the first process that
exceeds the limit used to end the analysis, and with it the answers the
other engines could still give. Past 80% of the limit (that of
--memory_limit, or else of the cgroup of the process), the engine whose
solvers use the most memory is now stopped, and the others go on.

The model is a loop of Euclid's algorithm on 32-bit vectors, whose
property holds: BMC can unroll it forever, and the remainders it adds at
every step make its solver grow by megabytes per step.
"""

import sys

import pytest

from conftest import run_kmoxi

gcd = """(set-logic QF_BV)
(define-system main :input ((i (_ BitVec 32)) (j (_ BitVec 32)))
  :output ((a (_ BitVec 32)) (b (_ BitVec 32))) :local ()
  :init (and (= a (bvor i #x00000001)) (= b j))
  :trans (and (= a' (ite (= b #x00000000) a b))
              (= b' (ite (= b #x00000000) b (bvurem a b)))))
(check-system main :input ((i (_ BitVec 32)) (j (_ BitVec 32)))
  :output ((a (_ BitVec 32)) (b (_ BitVec 32))) :local ()
  :reachable (r (= a #x00000000)) :query (q (r)))
"""


@pytest.mark.skipif(not sys.platform.startswith("linux"),
                    reason="the memory of the solvers is read from /proc")
def test_bmc_stopped_at_the_limit(tmp_path):
    path = tmp_path / "gcd.moxi"
    path.write_text(gcd)
    out, err = run_kmoxi(path, "--enable", "BMC", "--memory_limit", "500",
                         "-v", timeout=60)
    text = out + err
    assert "Stopping bounded model checking: its solvers use" in text, text
    # The analysis goes on to its response, without an answer for q
    assert ":query (q unknown" in text, text
