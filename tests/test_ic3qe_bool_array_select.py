"""IC3QE extracts a Boolean element of an array as an atom.

An element of an array of Booleans, (select a i), is a Boolean atom of the
transition system. The extraction of IC3QE, which picks the atoms a model
makes true, failed an assertion on it, as on any symbol it did not expect
at the top of an atom, and the engine stopped without an answer.
"""

import pytest

from conftest import run_kmoxi_process, query_answer

sort = "(Array (_ BitVec 2) Bool)"

# A constant array, read at a fixed index
constant = f"""(set-logic QF_ABV)
(declare-const u {sort})
(define-system main :input () :output ((n (_ BitVec 4))) :local ()
  :init (= n #x0) :trans (= n' (bvadd n #x1)))
(check-system main :input () :output ((n (_ BitVec 4))) :local ()
  :reachable (r (and (= n #x1) (select u #b10)))
  :query (q (r)))
"""

# A state array, read under a negation and at an index with an ite
state = f"""(set-logic QF_ABV)
(define-system main :input ((i (_ BitVec 2)) (b Bool))
  :output ((n (_ BitVec 4)) (a {sort})) :local ()
  :init (and (= n #x0) (= a ((as const {sort}) false)))
  :trans (and (= n' (bvadd n #x1)) (= a' (store a i' b'))))
(check-system main :input ((i (_ BitVec 2)) (b Bool))
  :output ((n (_ BitVec 4)) (a {sort})) :local ()
  :reachable (r (and (= n #x2) (select a #b01)
                     (not (select a (ite (= n #x2) #b10 #b11)))))
  :query (q (r)))
"""

# Only false is ever stored, so no element is true
unreachable = f"""(set-logic QF_ABV)
(define-system main :input ((i (_ BitVec 2)))
  :output ((a {sort})) :local ()
  :init (= a ((as const {sort}) false))
  :trans (= a' (store a i' false)))
(check-system main :input ((i (_ BitVec 2)))
  :output ((a {sort})) :local ()
  :reachable (r (select a #b10))
  :query (q (r)))
"""


@pytest.mark.parametrize(
    "model, answer",
    [(constant, "sat"), (state, "sat"), (unreachable, "unsat")],
    ids=["constant", "state", "unreachable"])
def test_ic3qe_answers(tmp_path, model, answer):
    path = tmp_path / "model.moxi"
    path.write_text(model)
    res = run_kmoxi_process(path, "--enable", "IC3QE", timeout=60)
    out = res.stdout + res.stderr
    assert "Assertion failed" not in out, out
    assert query_answer(out) == answer, out
