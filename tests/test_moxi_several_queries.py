"""kmoxi answers every query of a check-system (issue #1804).

kmoxi used to translate a check-system only with a single query of a single
:reachable condition, and no :current condition. The queries of a check
are now grouped by their assumptions and initiality condition, each group
with a system of its own, which its assumptions constrain and whose initial
states are those of its :current condition, if any: the condition replaces
the initial conditions of the checked system and of the systems it calls,
not their invariants. A query with several :reachable conditions has one
flag per condition, of whether it has held, and the witness ends where the
last one holds. The responses follow the order of the script. The queries
of a :queries attribute are separate queries, without declared constants.
"""

import re

import pytest

from conftest import run_kmoxi, query_answers

counter = """(set-logic QF_LIA)
(define-system main :input ((i Int)) :output ((n Int)) :local ()
  :init (= n 0) :trans (= n' (+ n (ite (> i' 0) 2 0))))
"""

check = "(check-system main :input ((i Int)) :output ((n Int)) :local ()\n"


def run(tmp_path, model):
    path = tmp_path / "model.moxi"
    path.write_text(model)
    out, err = run_kmoxi(path)
    return out + err


def trails(out):
    """The steps of each trail of `out` by query, each step a list of
    (name, value)"""
    return {
        name: [re.findall(r"\(((?:\|[^|]*\||[^\s()|]+)+) ([^\s()]+)\)", step)
               for step in re.findall(r"^\s*\(\d+ (.*)\)\s*$", trail, re.M)]
        for name, trail in re.findall(
            r":trail\s*\((\S+)_prefix \((.*?)\n\s*\)\s*\)", out, re.S)
    }


def values(steps, var):
    return [dict(step)[var] for step in steps]


# Queries of several groups, answered in the order of the script: n is even
# and never negative, stays 0 if i is never positive, and stays odd from 1
mixed = counter + check + """\
  :reachable (r (= n 2)) :reachable (s (= n 4)) :reachable (t (< n 0))
  :reachable (u (= n' 6)) :assumption (a (<= i' 0)) :current (c (= n 1))
  :query (q1 (r s)) :query (q2 (t)) :query (q3 (r a)) :query (q4 (c s))
  :query (q5 (c r)) :query (q6 (s u)) :query (q7 (r t)) :query (q8 (r)))
"""


def test_answers_in_script_order(tmp_path):
    out = run(tmp_path, mixed)
    assert query_answers(out) == [
        ("q1", "sat"), ("q2", "unsat"), ("q3", "unsat"), ("q4", "unsat"),
        ("q5", "unsat"), ("q6", "sat"), ("q7", "unsat"), ("q8", "sat"),
    ], out


def test_witness_of_several_conditions(tmp_path):
    out = run(tmp_path, mixed)
    t = trails(out)
    # Ends where the last condition holds, a state or a transition, and
    # shows no condition
    assert values(t["q1"], "n") == ["0", "2", "4"], out
    assert values(t["q6"], "n") == ["0", "2", "4", "6"], out
    assert all(len(step) == 2 for step in t["q1"] + t["q6"]), out
    # A condition of a query of its own is shown, in the same system
    assert t["q8"][-1] == [("i", "1"), ("n", "2"), ("r", "true")], out


# Conditions that hold in the initial state: a witness of one state
def test_conditions_of_the_initial_state(tmp_path):
    model = counter + check + """\
  :reachable (r (= n 0)) :reachable (s (>= n 0)) :query (q (r s)))
"""
    out = run(tmp_path, model)
    assert query_answers(out) == [("q", "sat")], out
    assert trails(out)["q"] == [[("i", "0"), ("n", "0")]], out


# The initiality condition replaces the initial condition of the called
# system too, but not its invariant
called = """(set-logic QF_LIA)
(define-system cnt :input ((i Int)) :output ((n Int)) :local ((m Int))
  :init (and (= n 0) (= m 0))
  :trans (and (= m' (+ m 1)) (= n' (+ n (ite (> i' 0) 2 0))))
  :inv (>= m 0))
(define-system main :input ((i Int)) :output ((n Int)) :local ()
  :subsys (c1 (cnt i n)))
(check-system main :input ((i Int)) :output ((n Int)) :local ()
  :current (c (= n 1)) :reachable (r (= n 3)) :reachable (z (= n 1))
  :query (q1 (c r)) :query (q2 (r z)) :query (q3 (c r z)) :query (q4 (c z)))
(check-system cnt :input ((i Int)) :output ((n Int)) :local ((m Int))
  :current (c (= n 1)) :reachable (r (< m 0)) :query (q5 (c r)))
"""


def test_current_condition(tmp_path):
    out = run(tmp_path, called)
    assert query_answers(out) == [
        ("q1", "sat"), ("q2", "unsat"), ("q3", "sat"), ("q4", "sat"),
        ("q5", "unsat"),
    ], out
    t = trails(out)
    assert values(t["q1"], "c1::n") == ["1", "3"], out
    assert values(t["q3"], "n") == ["1", "3"], out
    assert values(t["q4"], "n") == ["1"], out


# Without declared constants, the queries of a :queries attribute are
# separate queries
def test_queries_attribute(tmp_path):
    model = counter + check + """\
  :reachable (r (= n 2)) :reachable (s (< n 0)) :queries ((q1 (r)) (q2 (s))))
"""
    out = run(tmp_path, model)
    assert query_answers(out) == [("q1", "sat"), ("q2", "unsat")], out


# The copies of the systems a check with an initiality condition checks are
# named after its system, whose name is the prefix of no system of the
# script
def test_copies_have_fresh_names(tmp_path):
    model = """(set-logic QF_LIA)
(define-system __kmoxi_check_0_main :input () :output ((x Int))
  :init (= x 5) :trans (= x' x))
(define-system main :input () :output ((x Int))
  :init (= x 0) :trans (= x' (+ x 1)))
(check-system main :input () :output ((x Int))
  :current (c (= x 2)) :reachable (r (= x 1)) :query (q1 (c r)))
(check-system __kmoxi_check_0_main :input () :output ((x Int))
  :current (c (= x 1)) :reachable (r (= x 1)) :query (q2 (c r)))
"""
    out = run(tmp_path, model)
    assert query_answers(out) == [("q1", "unsat"), ("q2", "sat")], out
