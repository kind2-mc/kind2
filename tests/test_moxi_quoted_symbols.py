"""kmoxi quotes the symbols of its responses, and of its solver input, when
needed.

The names of the variables, systems, conditions, queries and what is named
after them, constants, enumeration sorts and values are printed as quoted
symbols when they are not simple SMT-LIB symbols, by the rule the solver
input follows: the solvers are given an uninterpreted function whose name
is not a simple symbol quoted. They used to be given the predicates of a
system named |the sys| as __node_init_the sys, which they rejected.
"""

import pytest

from conftest import run_kmoxi

quoted = """(set-logic QF_LIA)
(declare-enum-sort |traffic light| (|go now| stop))
(declare-const |my k| Int)
(define-system |the sys| :input () :output ((|x y| Int) (l |traffic light|))
  :local ((|2t| Int))
  :init (and (= |x y| 0) (= |2t| 0) (= l |go now|))
  :trans (and (= |x y|' (+ |x y| |my k|)) (= |2t|' (+ |2t| 1)) (= l' stop)))
(check-system |the sys| :input () :output ((|x y| Int) (l |traffic light|))
  :local ((|2t| Int))
  :reachable (|reach it| (and (= |2t| 2) (= |x y| 4) (= l stop)))
  :query (|q 1| (|reach it|)))
"""


def test_symbols_quoted(tmp_path):
    path = tmp_path / "model.moxi"
    path.write_text(quoted)
    out, err = run_kmoxi(path, "--enable", "BMC")
    for text in [
        ":query (|q 1| sat :model |q 1_model| :trace |q 1_trace|)",
        ":trace (|q 1_trace| :prefix |q 1_prefix|)",
        "(define-fun |my k| () Int 2)",
        "(|the sys|::|x y| 0)",
        "(|the sys|::l |go now|)",
        "(|the sys|::|2t| 0)",
        "(|reach it| true)",
    ]:
        assert text in out, out + err
    # Simple symbols are not quoted
    assert "|l|" not in out and "|stop|" not in out, out


# A system whose name is a simple symbol, and one whose name is that of the
# other made simple, which the predicates of the first used to be renamed to
names = {
    "simple": """(set-logic QF_LIA)
(define-system a-b :output ((x Int)) :init (= x 0) :trans (= x' (+ x 1)))
(check-system a-b :output ((x Int)) :reachable (r (= x 2)) :query (q (r)))
""",
    "simple form of another": """(set-logic QF_LIA)
(define-system |a b| :output ((x Int)) :init (= x 0) :trans (= x' (+ x 1)))
(define-system a_b :output ((x Int) (y Int)) :init (= x 5) :trans (= x' x))
(check-system |a b| :output ((x Int)) :reachable (r (= x 2)) :query (q (r)))
""",
}


@pytest.mark.parametrize("case", names, ids=names)
def test_system_names(tmp_path, case):
    path = tmp_path / "model.moxi"
    path.write_text(names[case])
    out, err = run_kmoxi(path, "--enable", "BMC")
    assert ":query (q sat" in out, out + err
