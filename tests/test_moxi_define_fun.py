"""kmoxi accepts define-fun, and gives the definitions to the solvers.

A function defined with define-fun is not recursive in SMT-LIB: its body
applies only its parameters and the functions defined before it. kmoxi
used to reject the command as a syntax error. It now type checks it, keeps
the applications of the function in the terms, and gives the solvers its
definition, as an SMT-LIB define-fun, before the predicates of the systems
that may apply it. The system stays in its quantifier-free logic, and no
engine is turned off for it, unlike the recursive functions of Lustre.

Each model below is answered with BMC and k-induction, with Z3 and, for the
bit-vector ones, with Bitwuzla when it is installed. The type errors are
reported before any analysis.
"""

import os
import re
import shutil
import subprocess

import pytest

from conftest import kill_tree, kmoxi_args, kmoxi_bin

# A counter stepped by a defined function, which applies an earlier one
nested = """
(set-logic QF_BV)
(define-fun one () (_ BitVec 4) #x1)
(define-fun inc ((b (_ BitVec 4))) (_ BitVec 4) (bvadd b one))
(define-fun twice ((b (_ BitVec 4))) (_ BitVec 4) (inc (inc b)))
(define-system main :input () :output ((c (_ BitVec 4))) :local ()
  :init (= c #x0) :trans (= c' (twice c)))
(check-system main :input () :output ((c (_ BitVec 4))) :local ()
  :reachable (odd (= ((_ extract 0 0) c) #b1)) :query (q (odd)))
"""

# A parameter named like a state variable denotes the parameter, and the
# argument of an application may be primed
shadowing = """
(set-logic QF_LIA)
(define-fun step ((x Int) (d Int)) Int (+ x d))
(define-system main :input ((d Int)) :output ((x Int)) :local ()
  :init (= x 0) :trans (= x' (step x (ite (> d' 0) 1 0))))
(check-system main :input ((d Int)) :output ((x Int)) :local ()
  :reachable (three (= x 3)) :query (q (three)))
"""

# The same counter, with a condition the definition makes unreachable
unreachable = """
(set-logic QF_BV)
(define-fun inc ((b (_ BitVec 4))) (_ BitVec 4) (bvadd b #x2))
(define-system main :input () :output ((c (_ BitVec 4))) :local ()
  :init (= c #x0) :trans (= c' (inc c)))
(check-system main :input () :output ((c (_ BitVec 4))) :local ()
  :reachable (odd (= ((_ extract 0 0) c) #b1)) :query (q (odd)))
"""

answers = [
    ("nested", nested, "unsat", ["z3", "bitwuzla"]),
    ("shadowing", shadowing, "sat", ["z3"]),
    ("unreachable", unreachable, "unsat", ["z3", "bitwuzla"]),
]
cases = [(name, model, expected, solver)
         for name, model, expected, solvers in answers for solver in solvers]


def run(tmp_path, model, extra):
    if not kmoxi_bin.exists():
        pytest.skip(f"{kmoxi_bin} is not built (make kmoxi)")
    path = tmp_path / "model.moxi"
    path.write_text(model)
    args = kmoxi_args | {"--timeout": "30"}
    arg_list = [arg for pair in args.items() for arg in pair]
    popen_args = {} if os.name == "nt" else {"start_new_session": True}
    proc = subprocess.Popen(
        [kmoxi_bin, *arg_list, *extra, str(path)],
        stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True, **popen_args,
    )
    try:
        stdout, stderr = proc.communicate(timeout=60)
    except subprocess.TimeoutExpired:
        kill_tree(proc)
        proc.communicate()
        pytest.fail("no answer after 60s")
    return proc.returncode, re.sub(r"\x1b\[[0-9;]*m", "", stdout + stderr)


@pytest.mark.parametrize(
    "name, model, expected, solver", cases,
    ids=[f"{n}-{s}" for n, _, _, s in cases],
)
def test_define_fun_answers(tmp_path, name, model, expected, solver):
    if shutil.which(solver) is None:
        pytest.skip(f"{solver} is not installed")
    smt_solver = "Bitwuzla" if solver == "bitwuzla" else "Z3"
    _, out = run(tmp_path, model,
                 ["--smt_solver", smt_solver, "--enable", "BMC", "--enable", "IND"])
    assert f":query (q {expected}" in out, out


def test_definition_given_to_solver(tmp_path):
    # The solver is given the definition, and the logic stays quantifier-free
    trace_dir = tmp_path / "out"
    _, out = run(tmp_path, unreachable,
                 ["--enable", "BMC", "--enable", "IND",
                  "--smt_trace", "--output_dir", str(trace_dir)])
    assert ":query (q unsat" in out, out
    traces = list(trace_dir.rglob("*.smt2"))
    assert traces, out
    text = traces[0].read_text()
    assert re.search(r"\(define-fun\s+inc\s", text), text[:2000]
    assert "(set-logic QF_BV)" in text, text[:2000]


errors = {
    "arity": (
        "(define-fun inc ((b Int)) Int (+ b 1))",
        "(inc x 1)",
        "'inc' expects 1 argument but is applied to 2 arguments",
    ),
    "argument sort": (
        "(define-fun inc ((b Int)) Int (+ b 1))",
        "(inc true)",
        "argument 1 of 'inc'",
    ),
    "body sort": (
        "(define-fun inc ((b Int)) Bool (+ b 1))",
        "x",
        "the body of function 'inc' has sort Int, but Bool is declared",
    ),
    "system variable in body": (
        "(define-fun inc ((b Int)) Int (+ x 1))",
        "x",
        "unbound variable 'x'",
    ),
    "primed parameter": (
        "(define-fun inc ((b Int)) Int (+ b' 1))",
        "x",
        "next-state variable b'",
    ),
    "redefinition": (
        "(define-fun inc ((b Int)) Int b) (define-fun inc ((b Int)) Int b)",
        "x",
        "function 'inc' is already defined",
    ),
}


@pytest.mark.parametrize("case", errors, ids=errors)
def test_define_fun_type_errors(tmp_path, case):
    definitions, next_x, message = errors[case]
    model = f"""
(set-logic QF_LIA)
{definitions}
(define-system main :input () :output ((x Int)) :local ()
  :init (= x 0) :trans (= x' {next_x}))
(check-system main :input () :output ((x Int)) :local ()
  :reachable (r (< x 0)) :query (q (r)))
"""
    code, out = run(tmp_path, model, ["--only_parse", "true"])
    assert code != 0 and message in out, out
