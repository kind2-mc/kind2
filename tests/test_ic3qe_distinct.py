"""IC3 with quantifier elimination handles distinct terms.

IC3QE generalizes its counterexamples to induction by extracting an
implicant from a model, and both that extraction and the evaluation of
terms in a model had no case for distinct: they failed an assertion on it,
and IC3QE stopped on every system whose formulas apply distinct, which MoXI
models do. distinct is now the conjunction of the disequalities of every
two of its arguments, in the simplification that evaluates terms, and in
the extraction, which takes the first pair of equal arguments when it is
to be false.

Each model is checked with IC3QE alone: counters stepped from 0 by the
given amounts, and a query in which distinct appears directly, or under
another operator, so that it is evaluated as a subterm.
"""

import re

import pytest

from conftest import run_kmoxi


def model(steps, query):
    names = "abc"[: len(steps)]
    vars_ = " ".join(f"({n} Int)" for n in names)
    init = " ".join(f"(= {n} 0)" for n in names)
    trans = " ".join(f"(= {n}' (+ {n} {d}))" for n, d in zip(names, steps))
    return f"""
(set-logic QF_LIA)
(define-system main :input () :output ({vars_}) :local ()
  :init (and {init}) :trans (and {trans}))
(check-system main :input () :output ({vars_}) :local ()
  :reachable (r {query}) :query (q (r)))
"""


# (steps of a, b, c), query, expected answer. With steps 1 and 1, a and b are
# equal in every state; with 1 and 2 they differ from the first step on.
cases = {
    "binary-sat": ([1, 2], "(distinct a b)", "sat"),
    "binary-unsat": ([1, 1], "(distinct a b)", "unsat"),
    "ternary-sat": ([1, 2, 3], "(distinct a b c)", "sat"),
    "ternary-unsat": ([1, 1, 3], "(distinct a b c)", "unsat"),
    "or-sat": ([1, 2, 1], "(or (distinct a b) (< c 0))", "sat"),
    "or-unsat": ([1, 1, 1], "(or (distinct a b) (< c 0))", "unsat"),
    "ite-sat": ([1, 2, 1], "(ite (distinct a b) (> c 5) (< c 0))", "sat"),
    "ite-unsat": ([1, 1, 1], "(ite (distinct a b) (> c 5) (< c 0))", "unsat"),
    "and-sat": ([1, 2, 1], "(and (distinct a b) (>= c 0))", "sat"),
    "and-unsat": ([1, 1, 1], "(and (distinct a b) (>= c 0))", "unsat"),
    "implies-unsat": ([1, 2, 1], "(not (=> (distinct a b) (>= c 0)))", "unsat"),
    "bool-eq-unsat": ([1, 1, 1], "(not (= (distinct a b) (< c 0)))", "unsat"),
}


@pytest.mark.parametrize("case", cases, ids=cases)
def test_ic3qe_distinct(tmp_path, case):
    steps, query, expected = cases[case]
    path = tmp_path / f"{case}.moxi"
    path.write_text(model(steps, query))
    stdout, stderr = run_kmoxi(path, "-v", "--enable", "IC3QE")
    out = re.sub(r"\x1b\[[0-9;]*m", "", stdout + stderr)
    assert "Assertion failed" not in out, out
    assert f":query (q :result {expected}" in out, out
