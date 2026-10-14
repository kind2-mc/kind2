"""kmoxi prints the invariant of a certificate as an SMT-LIB term over the
names of the check, quoted when needed.

It used to print it in Lustre syntax, with names as they are declared: the
check below was answered with `:inv (true and r 1)`, which is not an SMT-LIB
term, and a variable needing quoting lost its bars the same way (#1789).
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

# The symbols the invariant may mention: the names of the check, and those
# of the theory
names = {"|r 1|", "|x y|", "|z w|"}
theory = {"true", "false", "not", "and", "or", "=>", "=", "distinct", "ite",
          "<", "<=", ">", ">=", "+", "-", "*", "div", "mod", "abs"}

token = re.compile(r"\(|\)|\|[^|]*\||[^\s()|]+")


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


def check_term(term, out):
    """Every application in `term` has an operator of the theory in head
    position, and every other atom is a numeral or a name of the check"""
    if isinstance(term, list):
        assert term and term[0] in theory - {"true", "false"}, out
        for arg in term[1:]:
            check_term(arg, out)
    else:
        assert term in names or term in {"true", "false"} or term.isdigit(), out


@pytest.mark.parametrize(
    "engines, mentioned",
    [
        # The invariant found may or may not mention the variables
        ((), {"|r 1|"}),
        # IC3IA finds an invariant over the variables
        (("--enable", "IC3IA"), {"|r 1|", "|x y|", "|z w|"}),
    ],
    ids=["default", "IC3IA"],
)
def test_inv_is_smtlib_term(tmp_path, engines, mentioned):
    path = tmp_path / "model.moxi"
    path.write_text(model)
    out, err = run_kmoxi(path, *engines)
    # A long certificate is broken across lines
    out = re.sub(r"\s+", " ", out)
    assert ":query (|q 1| unsat :certificate |q 1_cert|)" in out, out + err
    prefix = ":certificate (|q 1_cert| :inv "
    assert prefix in out, out + err
    inv, rest = parse(out.split(prefix, 1)[1])
    assert rest[:2] == [":k", rest[1]] and rest[1].isdigit(), out
    check_term(inv, out)
    atoms = set(token.findall(out.split(prefix, 1)[1].split(" :k ", 1)[0]))
    assert mentioned <= atoms, out
