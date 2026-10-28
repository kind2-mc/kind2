"""kmoxi translates arrays indexed by integers (QF_ALIA).

kmoxi used to accept only arrays indexed by bit-vectors, whose index type
gives the indices a bound: 2^w for an index of w bits. An index of sort Int
has no bound. The engines read the value of an array from the solver as a
whole, a constant array with stores, so a bound is not needed to print it,
in the trail or in the :model, whatever its indices, negative or large.
"""

import re

import pytest

from conftest import run_kmoxi_process, query_answer

sort = "(Array Int Int)"

# Two stores, at a negative index and at one past 64 bits
stores = f"""(set-logic QF_ALIA)
(define-system main :input ((j Int) (v Int))
  :output ((n Int) (a {sort})) :local ()
  :init (and (= n 0) (= a ((as const {sort}) 0)))
  :trans (and (= n' (+ n 1)) (= a' (store a j v))))
(check-system main :input ((j Int) (v Int))
  :output ((n Int) (a {sort})) :local ()
  :reachable (r (and (= n 2) (= (select a (- 3)) 7)
                     (= (select a 100000000000000000000) (- 5))))
  :query (q (r)))
"""

# The array keeps its value: storing an element of its own changes nothing
unchanged = f"""(set-logic QF_ALIA)
(define-system main :input ((j Int))
  :output ((a {sort})) :local ()
  :init (= a ((as const {sort}) 0))
  :trans (= a' (store a j' (select a j'))))
(check-system main :input ((j Int))
  :output ((a {sort})) :local ()
  :reachable (r (= (select a (- 7)) 1))
  :query (q (r)))
"""

# A constant array, whose value is in the :model
constant = f"""(set-logic QF_ALIA)
(declare-const t {sort})
(define-system main :input ()
  :output ((n Int)) :local ()
  :init (= n 0)
  :trans (= n' (+ n (select t n))))
(check-system main :input ()
  :output ((n Int)) :local ()
  :reachable (r (= n (- 4)))
  :query (q (r)))
"""

engines = {"bmc": ["BMC"], "ic3qe": ["IC3QE"], "ic3ia": ["IC3IA"], "default": []}


def run(tmp_path, model, engine):
    path = tmp_path / "model.moxi"
    path.write_text(model)
    args = [a for e in engines[engine] for a in ("--enable", e)]
    res = run_kmoxi_process(path, *args, timeout=60)
    return res.stdout + res.stderr


@pytest.mark.parametrize("engine", engines)
def test_stores_in_trail(tmp_path, engine):
    out = run(tmp_path, stores, engine)
    assert query_answer(out) == "sat", out
    last = re.search(r"^\s*\(2 .*\(a (.*)\)\s+\(r true\)", out, re.M)
    assert last, out
    value = last.group(1)
    assert f"((as const {sort}) 0)" in value, value
    assert "(- 3) 7)" in value, value
    assert "100000000000000000000 (- 5))" in value, value


@pytest.mark.parametrize("engine", ["ic3qe", "default"])
def test_unchanged_array_is_proved(tmp_path, engine):
    out = run(tmp_path, unchanged, engine)
    assert query_answer(out) == "unsat", out
    assert ":certificate (q_cert :inv" in out, out


@pytest.mark.parametrize("engine", engines)
def test_constant_in_model(tmp_path, engine):
    out = run(tmp_path, constant, engine)
    assert query_answer(out) == "sat", out
    model = out.split(":model", 1)[1].split(":trail", 1)[0]
    assert f"(define-fun t () {sort} " in model, model
