"""kmoxi answers each check-system of a script on its own.

The system kmoxi builds for a check-system used to be named "query" for
every check, so all of them had the same scope and the same variables. Each
analysis looked its system up by that scope, and found the same one: a
script with two checks got the response of one of them, twice. Each check
now has a system of its own, numbered, under a name that no system of the
script has, and the responses follow the order of the script.
"""

import re

import pytest

from conftest import run_kmoxi

system = """(set-logic QF_LIA)
(define-system main :input () :output ((x Int)) :local ((t Int))
  :init (and (= x 0) (= t 0)) :trans (and (= x' (+ x 2)) (= t' (+ t 1))))
"""


def check(condition, reachable, query):
    return (
        "(check-system main :input () :output ((x Int)) :local ((t Int))\n"
        f"  :reachable ({condition} {reachable}) :query ({query} ({condition})))\n"
    )


def run(tmp_path, model):
    path = tmp_path / "model.moxi"
    path.write_text(model)
    out, err = run_kmoxi(path, "--enable", "BMC", "--enable", "IND")
    return out + err


# The conditions of the two checks have the same name, or different ones:
# x is never negative, and is 4 after two steps
@pytest.mark.parametrize("second", ["r", "s"], ids=["same-name", "other-name"])
def test_each_check_answered(tmp_path, second):
    model = (system + check("r", "(< x 0)", "q1")
             + check(second, "(and (= t 2) (= x 4))", "q2"))
    out = run(tmp_path, model)
    answers = re.findall(r":query \((\w+) (\w+)", out)
    assert answers == [("q1", "unsat"), ("q2", "sat")], out


# Systems named as the systems of the checks would be: the checks are named
# after none of the systems of the script, even one defined after them
clashing = """(set-logic QF_LIA)
(define-system __kmoxi_check_0 :input () :output ((x Int))
  :init (= x 0) :trans (= x' (+ x 1)))
(check-system __kmoxi_check_0 :input () :output ((x Int))
  :reachable (r (= x 3)) :query (q1 (r)))
(check-system __kmoxi_check_0 :input () :output ((x Int))
  :reachable (r (< x 0)) :query (q2 (r)))
(define-system __kmoxi_check_2 :input () :output ((y Int))
  :init (= y 0) :trans (= y' y))
(check-system __kmoxi_check_2 :input () :output ((y Int))
  :reachable (r (= y 1)) :query (q3 (r)))
"""


def test_check_names_are_fresh(tmp_path):
    out = run(tmp_path, clashing)
    answers = re.findall(r":query \((\w+) (\w+)", out)
    assert answers == [("q1", "sat"), ("q2", "unsat"), ("q3", "unsat")], out
