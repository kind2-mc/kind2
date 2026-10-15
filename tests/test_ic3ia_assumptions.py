"""IC3IA answers with each way of checking under assumptions.

IC3IA asserts the cubes of its frames once, under activation literals, and
checks each query assuming the literals of the frames it needs. The frame
of a blocked cube and its generalization come from the unsat core of those
assumptions. With `--check_sat_assume false`, the assumptions are named
assertions and the core comes from `get-unsat-core` instead. Yices 2 does
not accept both unsat cores and unsat assumptions on one instance, so IC3IA
only asks for the latter. The model where the state is reachable is that of
test_ic3ia_propagation; in the other one, IC3IA has to block cubes and
refine its abstraction to prove the state unreachable.
"""

import shutil

import pytest

from conftest import ic3ia_args, ic3ia_solver, run_kmoxi
from test_ic3ia_propagation import model as reachable_model

unreachable_model = """(set-logic QF_LIA)
(define-system main
 :input ()
 :output ((x Int) (y Int))
 :local ()
 :init (and (= x 0) (= y 0))
 :trans (and (= x' (ite (< x 9) (+ x 1) 0))
             (= y' (ite (< x 9) (+ y 2) 0)))
 :inv true)
(check-system main
 :input ()
 :output ((x Int) (y Int))
 :local ()
 :reachable (r (and (= x 9) (> y 18)))
 :query (q (r)))
"""


@pytest.mark.skipif(
    shutil.which(ic3ia_solver) is None, reason=f"{ic3ia_solver} is not installed"
)
@pytest.mark.parametrize(
    "model, answer",
    [(reachable_model, "sat"), (unreachable_model, "unsat")],
    ids=["reachable", "unreachable"],
)
@pytest.mark.parametrize(
    "solver_args",
    [
        (),
        ("--check_sat_assume", "false"),
        ("--smt_solver", "Yices2"),
    ],
    ids=["assuming", "named", "yices2"],
)
def test_ic3ia_answer(tmp_path, model, answer, solver_args):
    if "Yices2" in solver_args and shutil.which("yices-smt2") is None:
        pytest.skip("yices-smt2 is not installed")
    path = tmp_path / "model.moxi"
    path.write_text(model)
    args = [arg for pair in ic3ia_args.items() for arg in pair]
    out, err = run_kmoxi(path, *args, *solver_args)
    assert f":query (q {answer}" in out, out + err
    assert "rror" not in out + err, out + err
