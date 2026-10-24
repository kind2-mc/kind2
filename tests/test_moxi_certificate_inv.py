"""kmoxi prints the invariant of a certificate as an SMT-LIB term over the
names of the check, quoted when needed, extended with qualified names.

It used to print it in Lustre syntax, with names as they are declared: the
check below was answered with `:inv (true and r 1)`, which is not an SMT-LIB
term, and a variable needing quoting lost its bars the same way (#1789).

The variables are named as follows:
- a variable of the check by its name in the check;
- a variable of a subsystem instance by the path of the instances down to
  it, a qualified name with each name quoted on its own, `C1::l`, so that
  the instances of a system are told apart, and a path from a variable
  `|C1::l|` of the check;
- a variable of kmoxi's own, such as the one a reachability condition is
  encoded by, after an `@`, with which SMT-LIB reserves symbols for
  solvers, so that it is the name of no variable of the model.

A value of an enumeration sort is printed by its name, an atom over a
variable of such a sort that the engines took for an integer is written by
cases over its values, and a divisibility constraint is `(_ divisible n)`.
"""

import re

import pytest

from conftest import run_kmoxi

model = """(set-logic QF_LIA)
(define-system |the sys| :output ((|x y| Int) (|z w| Int))
  :init (and (= |x y| 0) (= |z w| 0))
  :trans (and (= |x y|' (+ |x y| 1)) (= |z w|' (+ |z w| 1))))
(check-system |the sys| :output ((|x y| Int) (|z w| Int))
  :reachable (|r 1| (not (= |x y| |z w|)))
  :query (|q 1| (|r 1|)))
"""

# The models, with the names their invariants may mention, and those they
# must mention, for the engines given
models = {
    "quoted": (model, {"|@r 1|", "|x y|", "|z w|"}),
    # Two instances of a system, and a variable of the caller of the same
    # name as theirs
    "instances": ("""(set-logic QF_LIA)
(define-system Counter :input () :output ((c Int)) :local ((l Int))
  :init (and (= l 0) (= c l)) :trans (and (= l' (+ l 1)) (= c' l')))
(define-system main :input () :output ((x Int) (y Int)) :local ((l Int))
  :init (= l 0) :trans (= l' (+ l 1))
  :subsys (C1 (Counter x)) :subsys (C2 (Counter y)))
(check-system main :input () :output ((x Int) (y Int)) :local ((l Int))
  :reachable (r (not (= x y))) :query (q (r)))
""", {"@r", "x", "y", "l", "C1::l", "C2::l", "C1::c", "C2::c"}),
    # A variable of the check named as a path, and a variable of an
    # instance whose name contains ::, next to an instance of that name
    "paths": ("""(set-logic QF_LIA)
(define-system Counter :input () :output ((c Int))
  :init (= c 7) :trans (= c' (+ c 1)))
(define-system Inner :input () :output ((|b::c| Int)) :local ((z Int))
  :subsys (b (Counter z))
  :init (= |b::c| 0) :trans (= |b::c|' (+ |b::c| 1)))
(define-system Main :input () :output ((|a::b::c| Int))
  :subsys (a (Inner |a::b::c|)))
(check-system Main :input () :output ((|a::b::c| Int))
  :reachable (r (< |a::b::c| 0)) :query (q (r)))
""", {"@r", "|a::b::c|", "a::|b::c|", "a::z", "a::b::c"}),
    # From blue, c stays blue: an invariant rules out blue, so that it
    # mentions c and values of its sort, whichever invariant is found
    "enum": ("""(set-logic QF_LIA)
(declare-enum-sort Color (red green blue))
(define-system main :input () :output ((c Color)) :local ()
  :init (= c red) :trans (= c' (ite (= c red) green (ite (= c green) red blue))))
(check-system main :input () :output ((c Color)) :local ()
  :reachable (r (= c blue)) :query (q (r)))
""", {"@r", "c", "red", "green", "blue"}),
    # QE gives divisibility constraints
    "divisible": ("""(set-logic QF_LIA)
(define-system main :input ((i Int)) :output ((x Int)) :local ()
  :init (= x 0) :trans (= x' (+ x (* 2 i))))
(check-system main :input ((i Int)) :output ((x Int)) :local ()
  :reachable (r (= x 1)) :query (q (r)))
""", {"@r", "x", "i"}),
}

theory = {"true", "false", "not", "and", "or", "=>", "=", "distinct", "ite",
          "<", "<=", ">", ">=", "+", "-", "*", "div", "mod", "abs"}

# A symbol, or a qualified name: symbols joined by :: without spaces
token = re.compile(r"\(|\)|(?:\|[^|]*\||[^\s()|]+)+")


def parse(text):
    """The first s-expression of `text`, as nested lists of atoms, and the
    rest of `text`"""
    tokens = token.findall(text)
    pos = 0

    def sexpr():
        nonlocal pos
        tok = tokens[pos]
        pos += 1
        if tok == "(":
            items = []
            while tokens[pos] != ")":
                items.append(sexpr())
            pos += 1
            return items
        assert tok != ")", text
        return tok

    return sexpr(), tokens[pos:]


def check_term(term, names, numerals, out):
    """Every application in `term` has an operator of the theory in head
    position, and every other atom is a name of the check, a name of
    kmoxi's own, or a numeral if [numerals]"""
    if isinstance(term, list):
        head = term[0] if term else None
        # (_ divisible n)
        if isinstance(head, list):
            assert head[:2] == ["_", "divisible"] and head[2].isdigit(), out
        else:
            assert head in theory - {"true", "false"}, out
        for arg in term[1:]:
            check_term(arg, names, numerals, out)
    else:
        # A variable of kmoxi's own, such as the init flag, which an
        # invariant may or may not mention, is named after an @
        internal = term.startswith("@") or term.startswith("|@")
        assert (term in names or internal or term in {"true", "false"}
                or numerals and term.isdigit()), out


@pytest.mark.parametrize(
    "case, engines, mentioned",
    [
        # The invariant found may or may not mention the variables
        ("quoted", (), {"|@r 1|"}),
        # IC3IA finds an invariant over the variables
        ("quoted", ("--enable", "IC3IA"), {"|@r 1|", "|x y|", "|z w|"}),
        ("instances", ("--enable", "IC3IA"), {"C1::l", "C2::l"}),
        ("paths", ("--enable", "IC3IA"), set()),
        ("enum", ("--enable", "IC3IA"), {"red", "green", "blue"}),
        ("divisible", ("--enable", "IC3QE"), {"divisible"}),
    ],
    ids=["default", "IC3IA", "instances", "paths", "enum", "divisible"],
)
def test_inv_is_smtlib_term(tmp_path, case, engines, mentioned):
    text, names = models[case]
    path = tmp_path / "model.moxi"
    path.write_text(text)
    out, err = run_kmoxi(path, *engines)
    # A long certificate is broken across lines
    out = re.sub(r"\s+", " ", out)
    query = "|q 1|" if case == "quoted" else "q"
    cert = "|q 1_cert|" if case == "quoted" else "q_cert"
    assert f":query ({query} :result unsat :certificate {cert})" in out, out + err
    prefix = f":certificate ({cert} :inv "
    assert prefix in out, out + err
    inv, rest = parse(out.split(prefix, 1)[1])
    assert rest[:2] == [":k", rest[1]] and rest[1].isdigit(), out
    # No integer stands for a value of an enumeration sort
    check_term(inv, names, case != "enum", out)
    atoms = set(token.findall(out.split(prefix, 1)[1].split(" :k ", 1)[0]))
    if case == "enum":
        # Some value of the sort, by its name: which ones depends on the
        # invariant found
        assert mentioned & atoms, out
    else:
        assert mentioned <= atoms, out
