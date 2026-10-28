"""IC3QE extracts the counterexample of a system with an array (#1794).

IC3QE extracts a concrete path along its trace of blocking clauses, one
state at a time: it constrains a state to its values in the model, and asks
the solver for a successor in the next clause. The value of an array is a
constant array with stores, and cvc5, Yices 2 and Bitwuzla do not take back
an equation with a constant array. cvc5 exited on it, Yices 2 failed on its
syntax, and Bitwuzla answered unknown, so the query was left unknown by
IC3QE. Before the arrays were read whole, the extraction failed an
assertion with every solver, Z3 included.

The state of the path now has the equations of the elements of an array of
few elements, which every solver takes. An array of more elements is still
constrained by its value, which only Z3 and MathSAT take: with another
solver, IC3QE stops as for an unsupported feature, rather than on a solver
error.
"""

import shutil

import pytest

from conftest import run_kmoxi_process, query_answer

# The system of the issue: the transition relation mentions the array only
# under false, and r is reachable at depth 2
small = """(set-logic QF_ABV)
(define-system main :input () :output ((p0 Bool) (p1 Bool) (p2 Bool) (m (Array (_ BitVec 2) (_ BitVec 2)))) :local ()
  :init (and (not p0) (not p2))
  :trans (or p0' (and p0 p1) (and false (= m' m))))
(check-system main :input () :output ((p0 Bool) (p1 Bool) (p2 Bool) (m (Array (_ BitVec 2) (_ BitVec 2)))) :local ()
  :reachable (r (and p2 (not p0))) :query (q (r)))
"""

# The array is written on the path, and read to take the step that reaches
# r, so that its values must be those of a path of the system
written = """(set-logic QF_ABV)
(define-system main :input () :output ((p0 Bool) (p1 Bool) (p2 Bool) (m {sort})) :local ()
  :init (and (not p0) (not p2) (= (select m {zero}) #b00))
  :trans (or (and p0' (= m' (store m {zero} #b01)))
             (and p0 p1 (= (select m {zero}) #b01))))
(check-system main :input () :output ((p0 Bool) (p1 Bool) (p2 Bool) (m {sort})) :local ()
  :reachable (r (and p2 (not p0))) :query (q (r)))
"""


def written_model(width):
    return written.format(
        sort=f"(Array (_ BitVec {width}) (_ BitVec 2))", zero="#b" + "0" * width
    )


# Each solver, with the name of its executable
solvers = {
    "Z3": "z3",
    "cvc5": "cvc5",
    "Yices2": "yices-smt2",
    "Bitwuzla": "bitwuzla",
    "MathSAT": "mathsat",
}


def run(tmp_path, model, solver):
    if shutil.which(solvers[solver]) is None:
        pytest.skip(f"{solvers[solver]} is not installed")
    path = tmp_path / "model.moxi"
    path.write_text(model)
    res = run_kmoxi_process(
        path, "--enable", "IC3QE", "--smt_solver", solver, "-v", timeout=30
    )
    out = res.stdout + res.stderr
    assert "Runtime error" not in out, out
    assert "Runtime failure" not in out, out
    assert "SMT solver died" not in out, out
    assert "resulted in `unknown`" not in out, out
    return res.stdout, out


@pytest.mark.parametrize("solver", solvers)
@pytest.mark.parametrize(
    "model", [small, written_model(2)], ids=["unconstrained", "written"]
)
def test_small_array(tmp_path, solver, model):
    stdout, out = run(tmp_path, model, solver)
    assert query_answer(stdout) == "sat", out
    assert "Property q disproved by IC3QE" in out, out


# An array of 2^9 elements, too many for the equations of its elements
@pytest.mark.parametrize("solver", solvers)
def test_large_array(tmp_path, solver):
    stdout, out = run(tmp_path, written_model(9), solver)
    if solver in ("Z3", "MathSAT"):
        assert query_answer(stdout) == "sat", out
        assert "Property q disproved by IC3QE" in out, out
    else:
        assert query_answer(stdout) == "unknown", out
        assert "IC3QE stops: a counterexample of the system has an array of more" in out, out
