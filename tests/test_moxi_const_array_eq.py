"""An equality with a constant array is expanded over the indices.

kmoxi translates an equality between an array and a constant array whose
index sort is a small bit-vector into the conjunction of the equalities
between each element and the constant. Bitwuzla 0.9 does not support an
equality over constant arrays under Boolean structure, which is where every
engine puts the initial-state constraint, and answered unknown on such
systems; with the expansion it answers. The expansion must keep the meaning
of the equality, which the satisfiable and unsatisfiable queries below check
with each solver, and an equality over an index too wide to expand is
translated as before.
"""

import os
import shutil
import subprocess

import pytest

from conftest import common_args, kill_tree, kmoxi_bin

# mem starts as the constant array 0; a step writes 1 at index 1 when w holds
system = """
(set-logic QF_ABV)
(define-system main
  :input ((w Bool) (i (_ BitVec {width}))) :output ((mem (Array (_ BitVec {width}) (_ BitVec 4)))) :local ()
  :init (= mem ((as const (Array (_ BitVec {width}) (_ BitVec 4))) #b0000))
  :trans (= mem' (ite w (store mem {one} #b0001) mem)))
"""

queries = {
    # An element other than 0 or 1: never
    "unsat": ":reachable (rch (and (not (= (select mem i) #b0000)) (not (= (select mem i) #b0001))))",
    # Element 1 is written
    "sat": ":reachable (rch (= (select mem i) #b0001))",
}

cases = [
    (solver, width, expected)
    for solver in ["z3", "bitwuzla"]
    for width, expected in [(2, "unsat"), (2, "sat"), (9, "sat")]
]


@pytest.mark.parametrize(
    "solver, width, expected",
    cases,
    ids=[f"{s}-index{w}-{e}" for s, w, e in cases],
)
def test_const_array_equality(tmp_path, solver, width, expected):
    if not kmoxi_bin.exists():
        pytest.skip(f"{kmoxi_bin} is not built (make kmoxi)")
    if shutil.which(solver) is None:
        pytest.skip(f"{solver} is not installed")

    model = system.format(width=width, one="#b" + "0" * (width - 1) + "1") + (
        "(check-system main :input ((w Bool) (i (_ BitVec {width})))"
        " :output ((mem (Array (_ BitVec {width}) (_ BitVec 4)))) :local ()"
        " {query} :query (q (rch)))\n"
    ).format(width=width, query=queries[expected])
    path = tmp_path / "mem.moxi"
    path.write_text(model)
    args = common_args | {"--timeout": "30"}
    arg_list = [arg for pair in args.items() for arg in pair]
    popen_args = {} if os.name == "nt" else {"start_new_session": True}
    proc = subprocess.Popen(
        [kmoxi_bin, *arg_list, "--smt_solver", solver,
         "--enable", "BMC", "--enable", "IND", str(path)],
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
        **popen_args,
    )
    try:
        stdout, stderr = proc.communicate(timeout=60)
    except subprocess.TimeoutExpired:
        kill_tree(proc)
        proc.communicate()
        pytest.fail("no answer after 60s")
    assert f":query (q {expected}" in stdout, stdout + stderr
