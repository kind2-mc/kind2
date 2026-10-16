"""kmoxi translates long chains of nested lets in a time and a memory about
linear in their length.

Translators write a formula with shared subterms as a chain of directly
nested lets, often thousands of them, each binding a subterm. kmoxi used to
translate each let on its own, and Kind 2 builds a let by traversing its
body, so a chain of 3000 lets took more than 3 GB and minutes before any
engine started. kmoxi now groups the bindings of a chain into one let per
level of dependency.

Kind 2 identifies the variable of a let binding by its name and type, so
moving a binding to another let could make it capture an occurrence of a
variable of the same name that it does not bind. A let of the chain that
rebinds a symbol of the chain, or a symbol that a term of an earlier let
takes from the enclosing scope, therefore starts a new group, and a let
with a term that refers to a symbol of its own bindings, which it takes
from the enclosing scope as well, is kept as it is.

In each model below, every step sets x, initially 0, to a value computed
by a chain of lets from z, which is always 0. Grouped without these
rules, the chain would compute another value; the tests check that x can
have the right value and not that one.
"""

import pytest

from conftest import run_kmoxi


def model(trans, value):
    return f"""(set-logic QF_LIA)
(define-system main :input () :output ((x Int) (z Int)) :local ()
  :init (and (= x 0) (= z 0))
  :trans (and (= z' z) {trans}))
(check-system main :input () :output ((x Int) (z Int)) :local ()
  :reachable (r (= x {value})) :query (q (r)))
"""


# The value of x after a step, and the value the chain would compute if its
# bindings were grouped by level alone
cases = {
    # The third let rebinds a, independently of the second: x' = 50 + 2.
    # Grouped by level, both bindings of a would be in the first let
    "rebinding": (
        "(let ((a (+ z 1))) (let ((c (+ a 1))) (let ((a 50))"
        " (= x' (+ a c)))))",
        52, 3,
    ),
    # c takes y from the enclosing let, 1, and the third let rebinds y:
    # x' = (0 + 1 + 1) + 100. Grouped by level, the binding of y would be
    # in the let around that of c: 201
    "symbol taken from the enclosing scope": (
        "(let ((y 1)) (= x' (let ((a (+ z 1))) (let ((c (+ a y)))"
        " (let ((y 100)) (+ c y))))))",
        102, 201,
    ),
    # The bindings of a let are simultaneous: c takes b from the enclosing
    # let, 7, not from its own: x' = 0 + 1 + 7. Grouped by level, the
    # binding of b would be in the let around that of c: 4
    "symbol of its own let": (
        "(let ((b 7)) (= x' (let ((a (+ z 1))) (let ((b 3) (c (+ a b)))"
        " c))))",
        8, 4,
    ),
    # A let inside a bound term, whose binding shadows a in its body only:
    # c = 10 + 1, then x' = c + a = 11 + 1
    "let in a bound term": (
        "(let ((a (+ z 1))) (let ((c (let ((a 10)) (+ a 1))))"
        " (= x' (+ c a))))",
        12, 21,
    ),
    # Independent and dependent bindings: e = 2, f = 3, g = 2 + 3 + 3
    "levels": (
        "(let ((e (+ z 2))) (let ((f (+ z 3))) (let ((g (+ e f f)))"
        " (let ((h (+ g 0))) (= x' h)))))",
        8, 5,
    ),
}


@pytest.mark.parametrize("name", cases)
def test_let_chain_scoping(tmp_path, name):
    trans, value, wrong = cases[name]
    path = tmp_path / "right.moxi"
    path.write_text(model(trans, value))
    out, err = run_kmoxi(path, "--enable", "BMC")
    assert ":query (q sat" in out, out + err
    path = tmp_path / "wrong.moxi"
    path.write_text(model(trans, wrong))
    out, err = run_kmoxi(path, "--enable", "BMC", "--enable", "IND")
    assert ":query (q unsat" in out, out + err


def long_chain(n):
    """A chain of 2n lets: n independent bindings e_i = x + i, then n
    bindings f_i = e_i > 0, each depending on one e_i, so two levels"""
    opens = [f"(let ((e{i} (+ x {i})))" for i in range(1, n + 1)]
    opens += [f"(let ((f{i} (> e{i} 0)))" for i in range(1, n + 1)]
    body = "(= x' (ite (and " + " ".join(f"f{i}" for i in range(1, n + 1))
    body += ") (+ x 1) x))"
    return " ".join(opens) + " " + body + ")" * (2 * n)


def test_long_let_chain(tmp_path):
    # 10000 lets, which took several gigabytes and minutes before
    path = tmp_path / "chain.moxi"
    path.write_text(model(long_chain(5000), 1))
    out, err = run_kmoxi(path, "--enable", "BMC", timeout=60)
    assert ":query (q sat" in out, out + err
