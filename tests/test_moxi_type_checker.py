"""kmoxi type checks a MoXI script before translating it.

The MoXI front end used to translate a parsed script straight into
transition systems. An ill-sorted model was either accepted, with the
solvers given nonsense (a Boolean output compared to 0 answered "sat" with a
trace), or rejected with an uncaught exception and a backtrace. The sort
checker now reports the first error with its position and a message, and
kmoxi exits with the parse error code. `--only_parse true` stops after the
check, which is how the ill-typed models below are run. Each case is a
model and a fragment of the expected message; the well-typed models are
run to an answer, since the constructs they use (the `!=` disequality, a
`(_ bvN m)` constant, a let shadowing a state variable) must also be
translated.
"""

import subprocess

import pytest

from conftest import common_args, kmoxi_bin, run_timeout

# Exit code of a parse or type error
PARSE_ERROR = 3


def kmoxi(path, *args):
    return subprocess.run(
        [kmoxi_bin, *args, str(path)],
        capture_output=True,
        text=True,
        timeout=run_timeout,
    )


def head(logic="QF_LIA", **vars):
    """The start of a main system with the given :input, :output and :local
    lists, on line 3 after the set-logic command; `logic=None` omits the
    set-logic command, for a main system after other systems."""
    inp = vars.get("input", "((x Int))")
    out = vars.get("output", "((y Int))")
    loc = vars.get("local", "()")
    logic = f"(set-logic {logic})\n" if logic else ""
    return f"{logic}(define-system main\n  :input {inp} :output {out} :local {loc}\n"


# A system other than main for the composite models, after the set-logic
sub = "(set-logic QF_LIA)\n(define-system Sub :input ((i {isort})) :output ((o Int)) :local ())\n"


# Each ill-typed model with the position (line:column) and a fragment of the
# message expected
ill_typed = {
    "unknown-logic": (
        "(set-logic QF_FOO)\n",
        "1:12", "unknown or unsupported logic 'QF_FOO'",
    ),
    "logic-twice": (
        "(set-logic QF_LIA)\n(set-logic QF_LIA)\n",
        "2:12", "already set",
    ),
    "logic-after-definition": (
        "(define-system main :input () :output () :local ())\n(set-logic QF_LIA)\n",
        "2:12", "must precede",
    ),
    "unknown-sort": (
        head(output="((y Foo))") + ")\n",
        "3:32", "unknown sort 'Foo'",
    ),
    "bitvec-width-zero": (
        head(logic="QF_BV", input="()", output="((y (_ BitVec 0)))") + ")\n",
        "3:25", "malformed sort '(_ BitVec 0)': the width must be positive",
    ),
    "array-arity": (
        head(logic="QF_ABV", input="()", output="((y (Array Int)))") + ")\n",
        "3:26", "malformed sort '(Array Int)': Array takes two sort parameters",
    ),
    "sort-not-in-logic": (
        head(output="((y (_ BitVec 8)))") + ")\n",
        "3:32", "sort (_ BitVec 8) is not in logic QF_LIA",
    ),
    "numeral-not-in-logic": (
        head(logic="QF_BV", input="()", output="((y (_ BitVec 8)))")
        + "  :init (= y 0))\n",
        "4:14", "numerals are not in logic QF_BV",
    ),
    "decimal-not-in-logic": (
        head() + "  :init (= y 0.5))\n",
        "4:14", "decimals are not in logic QF_LIA",
    ),
    "bitvector-not-in-logic": (
        head() + "  :init (= y #b0101))\n",
        "4:14", "bit-vector literals are not in logic QF_LIA",
    ),
    "symbol-not-in-logic": (
        head() + "  :init (= y (bvadd x x)))\n",
        "4:14", "symbol 'bvadd' is not in logic QF_LIA",
    ),
    "to_real-not-in-logic": (
        head() + "  :init (= (to_real y) (to_real x)))\n",
        "4:12", "symbol 'to_real' is not in logic QF_LIA",
    ),
    "nonlinear-product": (
        head() + "  :init (= y (* x x)))\n",
        "4:14", "nonlinear application of '*' in logic QF_LIA",
    ),
    "nonlinear-division": (
        head() + "  :init (= y (div 2 x)))\n",
        "4:14", "nonlinear application of 'div' in logic QF_LIA",
    ),
    "nonlinear-modulo": (
        head() + "  :init (= y (mod x (- x))))\n",
        "4:14", "nonlinear application of 'mod' in logic QF_LIA",
    ),
    "unbound-variable": (
        head() + "  :trans (= y' (+ z 1)))\n",
        "4:19", "unbound variable 'z'",
    ),
    "unknown-function": (
        head() + "  :init (foo x y))\n",
        "4:9", "unknown function symbol 'foo'",
    ),
    "unknown-indexed-function": (
        head(logic="QF_BV", input="()", output="((y (_ BitVec 8)))")
        + "  :init (= y ((_ foo 1) y)))\n",
        "4:14", "unknown indexed identifier '(_ foo 1)'",
    ),
    "bitvector-literal-out-of-range": (
        head(logic="QF_BV", input="()", output="((y (_ BitVec 8)))")
        + "  :init (= y (_ bv300 8)))\n",
        "4:14", "bit-vector literal (_ bv300 8) does not fit in 8 bits",
    ),
    "index-out-of-range": (
        head(logic="QF_BV", input="()", output="((y (_ BitVec 8)))")
        + "  :init (= ((_ extract 99999999999999999999 0) y) y))\n",
        "4:12", "unknown indexed identifier '(_ extract 99999999999999999999 0)'",
    ),
    "unknown-indexed-constant": (
        head(logic="QF_BV", input="()", output="((y (_ BitVec 8)))")
        + "  :init (= y (_ bvx 8)))\n",
        "4:14", "unknown indexed identifier '(_ bvx 8)'",
    ),
    "primed-let-variable": (
        head() + "  :trans (let ((z x)) (= y' z')))\n",
        "4:29", "'z' is bound by a let and cannot be primed",
    ),
    "primed-function": (
        head() + "  :trans (= y' (+' x 1)))\n",
        "4:17", "'+' cannot be primed",
    ),
    "prime-in-init": (
        head() + "  :init (= y' 0))\n",
        "4:12", "next-state variable y' in the :init condition of system main, "
        "which must be a one-state formula",
    ),
    "prime-in-inv": (
        head() + "  :inv (= y' x))\n",
        "4:11", "next-state variable y' in the :inv condition of system main",
    ),
    "primed-output-in-assumption": (
        head() + ")\n(check-system main :input ((x Int)) :output ((y Int)) :local ()\n"
        "  :assumption (a (> y' 0)) :reachable (r (> y 0)) :query (q (a r)))\n",
        "6:21", "next-state variable y' in the :assumption condition a, "
        "where only input variables may be primed",
    ),
    "arity": (
        head() + "  :init (not (= x 0) (= y 0)))\n",
        "4:9", "'not' expects 1 argument but is applied to 2 arguments",
    ),
    "arity-disequality": (
        head() + "  :init (!= x y 0))\n",
        "4:9", "'!=' expects 2 arguments but is applied to 3 arguments",
    ),
    "argument-sort": (
        head() + "  :init (= y (+ x true)))\n",
        "4:14", "argument 2 of '+' has sort Bool; expected Int, the sort of "
        "the first argument",
    ),
    "ite-branches": (
        head() + "  :init (= y (ite (> x 0) x true)))\n",
        "4:14", "argument 3 of 'ite' has sort Bool; expected Int, the sort of "
        "the second argument",
    ),
    "mixed-int-real": (
        head(logic="QF_LIRA") + "  :init (= y (+ x 1.5)))\n",
        "4:14", "argument 2 of '+' has sort Real; expected Int",
    ),
    "equality-bool-int": (
        head(output="((y Bool))") + "  :init (= y 0))\n",
        "4:9", "argument 2 of '=' has sort Int; expected Bool",
    ),
    "init-not-bool": (
        head() + "  :init y)\n",
        "4:9", "the :init condition of system main has sort Int; expected Bool",
    ),
    "reachable-not-bool": (
        head() + ")\n(check-system main :input ((x Int)) :output ((y Int)) :local ()\n"
        "  :reachable (r (+ y 1)) :query (q (r)))\n",
        "6:17", "the :reachable condition r has sort Int; expected Bool",
    ),
    "ascription": (
        head() + "  :init (= y (as x Bool)))\n",
        "4:18", "term of sort Int is ascribed the sort Bool",
    ),
    "const-array-without-sort": (
        head(logic="QF_ABV", input="()", output="((a (Array (_ BitVec 2) (_ BitVec 4))))")
        + "  :init (= a (const #b0000)))\n",
        "4:14", "'const' must be qualified with the sort of the array",
    ),
    "const-array-non-array-sort": (
        head(logic="QF_ABV", input="()", output="((a (Array (_ BitVec 2) (_ BitVec 4))))")
        + "  :init (= a ((as const (_ BitVec 4)) #b0000)))\n",
        "4:14", "'const' is qualified with the sort (_ BitVec 4), which is not "
        "an array sort",
    ),
    "const-array-element": (
        head(logic="QF_ABV", input="()", output="((a (Array (_ BitVec 2) (_ BitVec 4))))")
        + "  :init (= a ((as const (Array (_ BitVec 2) (_ BitVec 4))) #b00)))\n",
        "4:14", "argument 1 of 'const' has sort (_ BitVec 2); expected (_ BitVec 4)",
    ),
    "extract-out-of-range": (
        head(logic="QF_BV", input="()", output="((y (_ BitVec 8)))")
        + "  :init (= ((_ extract 8 0) y) y))\n",
        "4:12", "argument 1 of '(_ extract 8 0)' has sort (_ BitVec 8); expected "
        "a bit-vector sort of more than 8 bits",
    ),
    "concat-width": (
        head(logic="QF_BV", input="((x (_ BitVec 4)))", output="((y (_ BitVec 8)))")
        + "  :init (= y (concat x y)))\n",
        "4:9", "argument 2 of '=' has sort (_ BitVec 12); expected (_ BitVec 8)",
    ),
    "select-index": (
        head(logic="QF_ABV", input="((i (_ BitVec 3)))",
             output="((a (Array (_ BitVec 2) (_ BitVec 4))))")
        + "  :init (= (select a i) #b0000))\n",
        "4:12", "argument 2 of 'select' has sort (_ BitVec 3); expected "
        "(_ BitVec 2), the index sort of the array",
    ),
    "duplicate-let-binding": (
        head() + "  :init (let ((z x) (z y)) (= z 0)))\n",
        "4:21", "variable 'z' is bound twice by the same let",
    ),
    "system-redefined": (
        head() + ")\n" + head(logic=None) + ")\n",
        "5:16", "system 'main' is already defined",
    ),
    "unknown-system": (
        head() + "  :subsys (S (Sub x y)))\n",
        "4:15", "unknown system 'Sub'",
    ),
    "self-instantiation": (
        head() + "  :subsys (S (main x y)))\n",
        "4:15", "system 'main' cannot have itself as a subsystem",
    ),
    "duplicate-instance": (
        sub.format(isort="Int") + head(logic=None)
        + "  :subsys (S (Sub x y)) :subsys (S (Sub x y)))\n",
        "5:34", "duplicate subsystem instance name 'S'",
    ),
    "duplicate-variable": (
        head(output="((x Int))") + ")\n",
        "3:29", "duplicate variable 'x'",
    ),
    "subsystem-arity": (
        sub.format(isort="Int") + head(logic=None) + "  :subsys (S (Sub x)))\n",
        "5:3", "subsystem S: system Sub has 2 input and output variables but 1 is given",
    ),
    "subsystem-argument-sort": (
        sub.format(isort="Bool") + head(logic=None) + "  :subsys (S (Sub x y)))\n",
        "5:19", "subsystem S: variable x of sort Int is bound to i, which has sort Bool",
    ),
    "subsystem-output-to-input": (
        sub.format(isort="Int") + head(logic=None) + "  :subsys (S (Sub y x)))\n",
        "5:21", "subsystem S: input variable x is bound to the output o",
    ),
    "renaming-arity": (
        head() + ")\n(check-system main :input ((x Int)) :output ((y Int) (z Int)) :local ()\n"
        "  :reachable (r (> y 0)) :query (q (r)))\n",
        "5:37", "2 output variables declared but system main has 1",
    ),
    "renaming-missing-locals": (
        head(local="((l Int))") + ")\n(check-system main :input ((x Int)) :output ((y Int))\n"
        "  :reachable (r (> y 0)) :query (q (r)))\n",
        "5:1", "0 local variables declared but system main has 1",
    ),
    "renaming-sort": (
        head() + ")\n(check-system main :input ((x Int)) :output ((z Bool)) :local ()\n"
        "  :reachable (r z) :query (q (r)))\n",
        "5:46", "variable z has sort Bool but renames y, which has sort Int",
    ),
    "duplicate-condition": (
        head() + ")\n(check-system main :input ((x Int)) :output ((y Int)) :local ()\n"
        "  :reachable (r (> y 0)) :reachable (r (< y 0)) :query (q (r)))\n",
        "6:38", "duplicate condition name 'r'",
    ),
    "duplicate-query": (
        head() + ")\n(check-system main :input ((x Int)) :output ((y Int)) :local ()\n"
        "  :reachable (r (> y 0)) :query (q (r)) :query (q (r)))\n",
        "6:49", "duplicate query name 'q'",
    ),
    "unknown-condition": (
        head() + ")\n(check-system main :input ((x Int)) :output ((y Int)) :local ()\n"
        "  :reachable (r (> y 0)) :query (q (r s)))\n",
        "6:39", "query q refers to 's', which names no condition",
    ),
}



@pytest.mark.parametrize("name", ill_typed, ids=list(ill_typed))
def test_ill_typed_model_is_rejected(tmp_path, name):
    if not kmoxi_bin.exists():
        pytest.skip(f"{kmoxi_bin} is not built (make kmoxi)")

    model, position, message = ill_typed[name]
    path = tmp_path / "model.moxi"
    path.write_text(model)
    run = kmoxi(path, "--only_parse", "true")
    assert run.returncode == PARSE_ERROR, run.stdout + run.stderr
    assert run.stderr.startswith(f"{path}:{position}: error: "), run.stderr
    assert message in run.stderr, run.stderr
    assert "Backtrace" not in run.stderr, run.stderr


# Well-sorted scripts that kmoxi does not translate: reported like a type
# error, at a position, rather than with a backtrace. The translation runs
# after the check, so these are not only-parse runs.
check = (
    head() + ")\n(check-system main :input ((x Int)) :output ((y Int)) :local ()\n"
)
unsupported = {
    "operator": (
        head(logic="ALL", input="()", output="((y (_ BitVec 8)))")
        + "  :init (= y ((_ int2bv 8) 5)))\n",
        "4:14", "kmoxi does not support the function symbol '(_ int2bv 8)'",
    ),
    "array-index-sort": (
        head(logic="QF_ALIA", input="()", output="((a (Array Int Int)))")
        + "  :init (= (select a 0) 0))\n",
        "3:22", "kmoxi supports arrays indexed by bit-vectors only; a has sort "
        "(Array Int Int)",
    ),
    "no-query": (
        check + "  :reachable (r (> y 0)))\n",
        "5:1", "kmoxi requires a :query in every check-system",
    ),
    "two-queries": (
        check + "  :reachable (r (> y 0)) :query (q (r)) :query (q2 (r)))\n",
        "5:1", "kmoxi supports one :query per check-system",
    ),
    "query-without-reachable": (
        check + "  :assumption (a (> x 0)) :query (q (a)))\n",
        "5:1", "kmoxi requires a query to name a :reachable condition",
    ),
    "two-reachable-conditions": (
        check + "  :reachable (r (> y 0)) :reachable (s (< y 0)) :query (q (r s)))\n",
        "5:1", "kmoxi supports one :reachable condition per query",
    ),
}


@pytest.mark.parametrize("name", unsupported, ids=list(unsupported))
def test_unsupported_script_is_reported(tmp_path, name):
    if not kmoxi_bin.exists():
        pytest.skip(f"{kmoxi_bin} is not built (make kmoxi)")

    model, position, message = unsupported[name]
    path = tmp_path / "model.moxi"
    path.write_text(model)
    assert kmoxi(path, "--only_parse", "true").returncode == 0
    run = kmoxi(path, "--timeout", "30")
    assert run.returncode == PARSE_ERROR, run.stdout + run.stderr
    assert run.stderr.startswith(f"{path}:{position}: error: "), run.stderr
    assert message in run.stderr, run.stderr
    assert "Backtrace" not in run.stderr, run.stderr


# Well-typed models with the answer to their query
well_typed = {
    # Linear arithmetic with constant coefficients, including a let-bound
    # one, and shadowing of a state variable by a let
    "linear": (
        head(logic="QF_LIA")
        + "  :init (= y (* 2 x))\n"
        + "  :trans (let ((c 3) (x true)) (and x (= y' (+ (* c y) (div y 2) (mod y 2))))))\n"
        "(check-system main :input ((x Int)) :output ((y Int)) :local ()\n"
        "  :reachable (r (let ((x (- y))) (< x 0))) :query (q (r)))\n",
        "sat",
    ),
    # Numerals are reals in a logic with reals only
    "reals": (
        head(logic="QF_LRA", input="((x Real))", output="((y Real))")
        + "  :init (and (<= 0 x 2) (= y (/ x 2)))\n  :trans (= y' (* (/ 1 2) x')))\n"
        "(check-system main :input ((x Real)) :output ((y Real)) :local ()\n"
        "  :reachable (r (> y (- x 0.5) 1)) :query (q (r)))\n",
        "unsat",
    ),
    # Bit-vector constants in both syntaxes, the disequality of MoXI, and
    # indexed operators
    "bitvectors": (
        head(logic="QF_BV", input="((x (_ BitVec 4)))", output="((y (_ BitVec 8)))")
        + "  :init (= y (concat x ((_ extract 3 0) (_ bv5 8))))\n"
        + "  :trans (= y' (concat #x0 (bvadd x' #x1))))\n"
        "(check-system main :input ((x (_ BitVec 4))) :output ((y (_ BitVec 8))) :local ()\n"
        "  :reachable (r (!= ((_ extract 3 0) y) ((_ extract 3 0) (_ bv5 8))))\n"
        "  :query (q (r)))\n",
        "sat",
    ),
    # A subsystem, and an assumption priming an input
    "composite": (
        "(set-logic QF_LIA)\n"
        "(define-system Delay :input ((i Int)) :output ((o Int)) :local ()\n"
        "  :init (= o 0) :trans (= o' i))\n"
        "(define-system main :input ((x Int)) :output ((y Int)) :local ((t Int))\n"
        "  :subsys (D1 (Delay x t)) :subsys (D2 (Delay t y)))\n"
        "(check-system main :input ((x Int)) :output ((y Int)) :local ((t Int))\n"
        "  :assumption (a (and (>= x 0) (> x' x))) :reachable (r (> y t)) :query (q (a r)))\n",
        "unsat",
    ),
}


@pytest.mark.parametrize("name", well_typed, ids=list(well_typed))
def test_well_typed_model_is_checked(tmp_path, name):
    if not kmoxi_bin.exists():
        pytest.skip(f"{kmoxi_bin} is not built (make kmoxi)")

    model, answer = well_typed[name]
    path = tmp_path / "model.moxi"
    path.write_text(model)
    assert kmoxi(path, "--only_parse", "true").returncode == 0
    args = common_args | {"--timeout": "30"}
    arg_list = [arg for pair in args.items() for arg in pair]
    run = kmoxi(path, *arg_list, "--enable", "BMC", "--enable", "IND")
    assert f":query (q {answer}" in run.stdout, run.stdout + run.stderr
