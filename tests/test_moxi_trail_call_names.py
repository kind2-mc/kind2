"""The trail names the variables of a subsystem by the path of the calls.

The trail used to name the variables of a subsystem after the system
called, so that two calls of a system had the same names, and listed the
locals of each call once more, under their bare names, at the level of the
caller. The variables of the check are now named as the check-system
declares them, those of each call by the path of the call names down to it,
each name quoted on its own, and each variable is listed once. Since the
`::` of a path is outside any quoted name, the path c1::c is told apart from
a variable |c1::c| of the check, and a::b::c from a variable |b::c| of the
call a. A condition named after a variable of the check is rejected.
"""

import re

from conftest import run_kmoxi

two_calls = """(set-logic QF_LIA)
(define-system Counter :input ((inc Bool)) :output ((c Int)) :local ((d Int))
  :init (and (= c 0) (= d 0))
  :trans (and (= c' (ite inc (+ c 1) c)) (= d' (+ d 1))))
(define-system Main :input ((a Bool) (b Bool)) :output ((x Int) (y Int))
  :subsys (c1 (Counter a x))
  :subsys (c2 (Counter b y)))
(check-system Main :input ((a Bool) (b Bool)) :output ((x Int) (y Int))
  :reachable (r (and (= x 2) (= y 0))) :query (q (r)))
"""

# Nested calls, a callee without locals, a call name to quote, and checks
# whose variables have names of their own
nested = """(set-logic QF_LIA)
(define-system Counter :input ((inc Bool)) :output ((c Int))
  :init (= c 0) :trans (= c' (ite inc (+ c 1) c)))
(define-system Pair :input ((a Bool)) :output ((x Int)) :local ((t Int) (y Int))
  :subsys (k1 (Counter a x))
  :subsys (|k 2| (Counter a y))
  :init (= t 5) :trans (= t' (+ t 1)))
(define-system Main :input ((p Bool)) :output ((u Int)) :local ((m Int))
  :subsys (left (Pair p u))
  :subsys (right (Pair p m)))
(check-system Main :input ((pp Bool)) :output ((uu Int)) :local ((mm Int))
  :reachable (r (= uu 1)) :query (q (r)))
(check-system Pair :input ((i Bool)) :output ((o Int)) :local ((l Int) (n Int))
  :reachable (s (= o 1)) :query (q2 (s)))
"""


def trails(tmp_path, model):
    path = tmp_path / "model.moxi"
    path.write_text(model)
    out, err = run_kmoxi(path, "--enable", "BMC")
    # The steps of each trail, each a list of (name, value)
    return [
        [re.findall(r"\(((?:\|[^|]*\||[^\s()|]+)+) ([^\s()]+)\)", step)
         for step in re.findall(r"^\s*\(\d+ (.*)\)\s*$", trail, re.M)]
        for trail in out.split(":trail")[1:]
    ], out + err


def test_two_calls(tmp_path):
    [steps], out = trails(tmp_path, two_calls)
    assert [n for n, _ in steps[0]] == [
        "a", "b", "x", "y",
        "c1::inc", "c1::c", "c1::d",
        "c2::inc", "c2::c", "c2::d",
        "r",
    ], out
    last = dict(steps[-1])
    assert (last["c1::c"], last["c2::c"]) == ("2", "0"), out
    assert (last["c1::d"], last["c2::d"]) == ("2", "2"), out


def test_nested_calls(tmp_path):
    [main, pair], out = trails(tmp_path, nested)
    calls = ["k1::inc", "k1::c", "|k 2|::inc", "|k 2|::c"]
    pair_vars = ["a", "x", "t", "y"]
    assert [n for n, _ in main[0]] == (
        ["pp", "uu", "mm"]
        + [f"{c}::{v}" for c in ["left", "right"]
           for v in pair_vars + calls]
        + ["r"]
    ), out
    assert [n for n, _ in pair[0]] == (
        ["i", "o", "l", "n"] + calls + ["s"]
    ), out
    assert dict(main[0])["left::t"] == "5", out


# A check variable named after a call path, and a call variable whose name
# contains :: next to a call of that name
aliases = """(set-logic QF_LIA)
(define-system Counter :input ((i Bool)) :output ((c Int))
  :init (= c 7) :trans (= c' (ite i (+ c 1) c)))
(define-system Inner :input ((i Bool)) :output ((|b::c| Int)) :local ((z Int))
  :subsys (b (Counter i z))
  :init (= |b::c| 0) :trans (= |b::c|' (+ |b::c| 1)))
(define-system Main :input ((p Bool)) :output ((|a::b::c| Int))
  :subsys (a (Inner p |a::b::c|)))
(check-system Main :input ((p Bool)) :output ((|a::b::c| Int))
  :reachable (r (= |a::b::c| 1)) :query (q (r)))
"""


def test_paths_do_not_alias(tmp_path):
    [steps], out = trails(tmp_path, aliases)
    names = [n for n, _ in steps[0]]
    assert names == [
        "p", "|a::b::c|", "a::i", "a::|b::c|", "a::z", "a::b::i", "a::b::c",
        "r",
    ], out
    first = dict(steps[0])
    assert (first["|a::b::c|"], first["a::b::c"]) == ("0", "7"), out
