"""kmoxi accepts declare-enum-sort and declare-const.

kmoxi used to reject both commands as syntax errors.

An enumeration sort, declared with declare-enum-sort, has exactly its
declared values. kmoxi translates it into an enumerated type of Kind 2, which
stands for a range of the integers, one per value. The systems constrain
their variables of the sort to the range in every state, and the trail gives
values by name.

A constant, declared with declare-const, keeps its value in every state, and
is the same in every system and function that mentions it. kmoxi translates
it into a constant state variable, which every system has as a global
constant. The value of each constant is given in the :model of a sat
answer, as SMT-LIB define-fun commands, rather than in the trail.

The type checker gives each enumeration value and constant a name of its
own, and rejects priming them.
"""

import re
import shutil
import subprocess

import pytest

from conftest import kill_tree, kmoxi_args, kmoxi_bin

# Exit code of a parse or type error
PARSE_ERROR = 3

color = """
(declare-enum-sort Color (red green blue))
(define-fun code ((col Color)) Int
  (ite (= col red) 1 (ite (= col green) 2 (ite (= col blue) 3 4))))
"""

# The value of an output of the sort, which no condition constrains, is one
# of the values: code e is never 4, neither initially nor after a step
unconstrained = f"""
(set-logic QF_LIA)
{color}
(define-system main :input () :output ((e Color) (n Int)) :local ()
  :init (= n 0) :trans (= n' (+ n 1)))
(check-system main :input () :output ((e Color) (n Int)) :local ()
  :reachable (r (= (code e) 4)) :query (q (r)))
"""

# The same for an input, primed in :trans, and a value with an ascription
primed_input = f"""
(set-logic QF_LIA)
{color}
(define-system main :input ((c Color)) :output ((n Int)) :local ()
  :init (= n 0) :trans (= n' (code c')))
(check-system main :input ((c Color)) :output ((n Int)) :local ()
  :reachable (r (or (= n 4) (= c (as red Color)) false)) :query (q (r)))
"""

# The trail names the values: s goes red, green, blue
trail = f"""
(set-logic QF_LIA)
{color}
(define-system main :input () :output ((s Color)) :local ()
  :init (= s red) :trans (= s' (ite (= s red) green blue)))
(check-system main :input () :output ((s Color)) :local ()
  :reachable (r (= s blue)) :query (q (r)))
"""

# A constant keeps its value: x = t * k, and the answer fixes k
rigid = """
(set-logic QF_LIA)
(declare-const k Int)
(define-system main :input () :output ((x Int)) :local ((t Int))
  :init (and (= x 0) (= t 0)) :trans (and (= x' (+ x k)) (= t' (+ t 1))))
(check-system main :input () :output ((x Int)) :local ((t Int))
  :reachable (r (and (= t 3) (= x 6))) :query (q (r)))
"""

# The same constant in a subsystem, a function body and a check-system
shared = """
(set-logic QF_LIA)
(declare-const k Int)
(define-fun step () Int k)
(define-system Acc :input () :output ((x Int)) :local ()
  :init (= x 0) :trans (= x' (+ x step)))
(define-system main :input () :output ((x Int)) :local ((t Int))
  :subsys (A (Acc x))
  :init (= t 0) :trans (= t' (+ t 1)))
(check-system main :input () :output ((x Int)) :local ((t Int))
  :reachable (r (and (= t 3) (= x 6) (> k 0))) :query (q (r)))
"""

# A constant of an enumeration sort: it has one of the values, and the
# model names it
enum_const = f"""
(set-logic QF_LIA)
{color}
(declare-const col Color)
(define-system main :input () :output ((s Color)) :local ()
  :init (= s red) :trans (= s' (ite (= s red) green blue)))
(check-system main :input () :output ((s Color)) :local ()
  :reachable (r (and (= s col) (distinct col red green))) :query (q (r)))
"""

enum_const_range = f"""
(set-logic QF_LIA)
{color}
(declare-const col Color)
(define-system main :input () :output ((n Int)) :local ()
  :init (= n (code col)) :trans (= n' n))
(check-system main :input () :output ((n Int)) :local ()
  :reachable (r (= n 4)) :query (q (r)))
"""

# An enumeration sort in a logic without integers
bitvectors = f"""
(set-logic QF_BV)
(declare-enum-sort Mode (idle busy))
(declare-const limit (_ BitVec 4))
(define-system main :input ((go Bool)) :output ((m Mode) (c (_ BitVec 4))) :local ()
  :init (and (= m idle) (= c #x0))
  :trans (and (= m' (ite go' busy m)) (= c' (ite (= m busy) (bvadd c #x1) c))))
(check-system main :input ((go Bool)) :output ((m Mode) (c (_ BitVec 4))) :local ()
  :reachable (r (and (= m busy) (= c limit) (bvugt limit #x2))) :query (q (r)))
"""

engines = {
    "ind": ["--enable", "BMC", "--enable", "IND"],
    "ic3qe": ["--enable", "IC3QE"],
    "ic3ia": ["--enable", "IC3IA"],
}

answers = [
    ("unconstrained", unconstrained, "unsat", ["ind", "ic3qe", "ic3ia"]),
    ("primed_input", primed_input, "sat", ["ind"]),
    ("trail", trail, "sat", ["ind"]),
    ("rigid", rigid, "sat", ["ind", "ic3ia"]),
    ("shared", shared, "sat", ["ind", "ic3ia"]),
    ("enum_const", enum_const, "sat", ["ind"]),
    ("enum_const_range", enum_const_range, "unsat", ["ind", "ic3qe", "ic3ia"]),
    ("bitvectors", bitvectors, "sat", ["ind"]),
]
cases = [(name, model, expected, engine)
         for name, model, expected, es in answers for engine in es]


def run(tmp_path, model, extra):
    if not kmoxi_bin.exists():
        pytest.skip(f"{kmoxi_bin} is not built (make kmoxi)")
    path = tmp_path / "model.moxi"
    path.write_text(model)
    args = kmoxi_args | {"--timeout": "30"}
    arg_list = [arg for pair in args.items() for arg in pair]
    proc = subprocess.Popen(
        [kmoxi_bin, *arg_list, *extra, str(path)],
        stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True,
        start_new_session=True,
    )
    try:
        stdout, stderr = proc.communicate(timeout=60)
    except subprocess.TimeoutExpired:
        kill_tree(proc)
        proc.communicate()
        pytest.fail("no answer after 60s")
    return proc.returncode, re.sub(r"\x1b\[[0-9;]*m", "", stdout + stderr)


@pytest.mark.parametrize(
    "name, model, expected, engine", cases,
    ids=[f"{n}-{e}" for n, _, _, e in cases],
)
def test_answers(tmp_path, name, model, expected, engine):
    if shutil.which("z3") is None:
        pytest.skip("z3 is not installed")
    _, out = run(tmp_path, model, ["--smt_solver", "Z3", *engines[engine]])
    assert f":query (q {expected}" in out, out


def test_trail_names_values(tmp_path):
    _, out = run(tmp_path, trail, ["--enable", "BMC"])
    steps = re.findall(r"\(main::s (\w+)\)", out)
    assert steps == ["red", "green", "blue"], out


def test_model_gives_constants(tmp_path):
    _, out = run(tmp_path, rigid, ["--enable", "BMC"])
    assert "(define-fun k () Int 2)" in out, out
    # A constant is in the model, not in the trail
    assert "k " not in out.split(":trail")[1], out
    _, out = run(tmp_path, shared, ["--enable", "BMC"])
    assert "(define-fun k () Int 2)" in out, out
    _, out = run(tmp_path, enum_const, ["--enable", "BMC"])
    assert "(define-fun col () Color blue)" in out, out


def check_head(declarations, logic="QF_LIA"):
    return f"(set-logic {logic})\n{declarations}\n"


main = """(define-system main :input ((c Color)) :output ((x Int)) :local ()
  :init (= x 0) :trans {trans})
"""

errors = {
    "unknown sort": (
        "(declare-const k Colour)",
        "(= x' x)",
        "3:18: error: unknown sort 'Colour'",
    ),
    "builtin sort": (
        "(declare-enum-sort Int (a b))",
        "(= x' x)",
        "sort 'Int' is already declared",
    ),
    "sort twice": (
        "(declare-enum-sort Color (red))",
        "(= x' x)",
        "sort 'Color' is already declared",
    ),
    "value twice": (
        "(declare-enum-sort Light (on red))",
        "(= x' x)",
        "'red' is already declared, as a constant",
    ),
    "value repeated": (
        "(declare-enum-sort Light (on on))",
        "(= x' x)",
        "'on' is already declared",
    ),
    "constant named as a value": (
        "(declare-const green Int)",
        "(= x' x)",
        "'green' is already declared",
    ),
    "constant twice": (
        "(declare-const k Int) (declare-const k Bool)",
        "(= x' x)",
        "'k' is already declared",
    ),
    "function named as a constant": (
        "(declare-const k Int) (define-fun k () Int 1)",
        "(= x' x)",
        "'k' is already declared",
    ),
    "builtin constant": (
        "(declare-const distinct Int)",
        "(= x' x)",
        "'distinct' is a built-in symbol",
    ),
    "primed constant": (
        "(declare-const k Int)",
        "(= x' k')",
        "'k' cannot be primed",
    ),
    "primed value": (
        "",
        "(= c' red')",
        "'red' cannot be primed",
    ),
    "sorts differ": (
        "(declare-enum-sort Light (on off))",
        "(and (= x' x) (= c on))",
        "argument 2 of '=' has sort Light; expected Color",
    ),
    "value is not an integer": (
        "",
        "(= x' (+ x red))",
        "argument 2 of '+' has sort Color",
    ),
    # A constant is not a constant term of the theory
    "nonlinear": (
        "(declare-const k Int)",
        "(= x' (* k x))",
        "nonlinear application of '*'",
    ),
}


@pytest.mark.parametrize("case", errors, ids=errors)
def test_type_errors(tmp_path, case):
    declarations, trans, message = errors[case]
    model = (check_head("(declare-enum-sort Color (red green blue))\n"
                        + declarations)
             + main.format(trans=trans))
    code, out = run(tmp_path, model, ["--only_parse", "true"])
    assert code == PARSE_ERROR and message in out, out


def test_logic_before_declarations(tmp_path):
    code, out = run(tmp_path, "(declare-const k Int)\n(set-logic QF_LIA)\n",
                    ["--only_parse", "true"])
    assert code == PARSE_ERROR and "2:12: error: set-logic must precede" in out, out


def test_array_of_enum_unsupported(tmp_path):
    model = (check_head("(declare-enum-sort Color (red green))", logic="QF_ABV")
             + "(define-system main :input () :output ((a (Array (_ BitVec 2) Color)))"
             + " :local ())\n"
             + "(check-system main :input () :output ((a (Array (_ BitVec 2) Color)))"
             + " :local () :reachable (r true) :query (q (r)))\n")
    code, out = run(tmp_path, model, ["--only_parse", "true"])
    assert code == 0, out
    code, out = run(tmp_path, model, [])
    assert code == PARSE_ERROR, out
    assert "kmoxi does not support arrays of an enumeration sort" in out, out
