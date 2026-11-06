"""The :model of a kmoxi response is (name M), with M one S-expression.

The MoXI definition gives the attribute as `:model (m M)`, with M an
interpretation in SMT-LIB format, which is a list of define-fun commands as
in the response to get-model. kmoxi printed `(m ())` for a system with no
constants, but listed the commands of the others next to the name, as
`(m (define-fun a ...) (define-fun b ...))`.
"""

import re

import pytest

from conftest import kmoxi_bin, query_answer, run_kmoxi

TOKEN = re.compile(r"\(|\)|\|[^|]*\||[^\s()|]+")


def parse(text):
    """The S-expression at the start of `text`, as nested lists of tokens"""
    stack = [[]]
    for token in TOKEN.findall(text):
        if token == "(":
            stack.append([])
        elif token == ")":
            done = stack.pop()
            stack[-1].append(done)
            if len(stack) == 1:
                return done
        else:
            stack[-1].append(token)
    raise ValueError(f"unbalanced: {text}")


def model_of(tmp_path, script):
    path = tmp_path / "model.moxi"
    path.write_text(script)
    if not kmoxi_bin.exists():
        pytest.skip(f"{kmoxi_bin} is not built (make kmoxi)")
    out, _ = run_kmoxi(path, "--enable", "BMC")
    assert query_answer(out) == "sat", out
    return parse(out.split(":model", 2)[2]), out


def script(declarations, reachable):
    return f"""
(set-logic QF_LIA)
{declarations}
(define-system main :input () :output ((x Int)) :local ()
  :init (= x 0) :trans (= x' (+ x 1)))
(check-system main :input () :output ((x Int)) :local ()
  :reachable (r {reachable}) :query (q (r)))
"""


@pytest.mark.parametrize(
    "declarations, reachable, names",
    [
        ("", "(= x 1)", []),
        ("(declare-const a Int)", "(= x (+ a 1))", ["a"]),
        (
            "(declare-const a Int) (declare-const |b c| Int)",
            "(and (= x 1) (< a |b c|))",
            ["a", "|b c|"],
        ),
    ],
    ids=["no-constant", "one-constant", "two-constants"],
)
def test_model_is_a_name_and_a_list(tmp_path, declarations, reachable, names):
    model, out = model_of(tmp_path, script(declarations, reachable))
    assert len(model) == 2, out
    name, interpretation = model
    assert name == "q_model", out
    assert [d[0] for d in interpretation] == ["define-fun"] * len(names), out
    assert [d[1] for d in interpretation] == names, out
