"""A MoXI query over the current state is evaluated in that state.

The reachable condition of a check-system query used to be stored shifted
by one step: the reserved variable standing for it was true in the initial
state and, after every transition, equal to the condition over the previous
state. A state satisfying the condition was then only observed through a
transition out of it, and a state without successors, which is how the
error location of a CHC translation ends, was never observed: the query
was reported unsatisfiable. A one-state assumption had the mirror problem:
enforced through the transition, it did not constrain the last state of a
counterexample.

Each case is run under the engines that answer it: BMC for a satisfiable
query, so that the trace is the one it found, and BMC with k-induction for
an unsatisfiable one.
"""

import os
import re
import subprocess

import pytest

from conftest import common_args, kill_tree, kmoxi_bin

# kmoxi does not stop at its --timeout yet, and an engine that cannot
# answer would run until pytest's backstop: these cases settle in well
# under a second, so give up after a minute and fail. The run leads a
# process group of its own, so that its solvers, which hold the output
# pipes, are killed with it (see `kill_tree`)
moxi_timeout = 60

# x counts up; err is raised in the state after x = 3, and no transition
# leaves a state where err holds
system = """
(set-logic QF_LIA)
(define-system main
  :input () :output ((x Int) (err Bool)) :local ()
  :init (and (= x 0) (not err))
  :trans (and (not err) (= x' (+ x 1)) (= err' (= x 3)))
  :inv true)
"""

cases = {
    # The error state has no successor, and must be found all the same
    "deadlocked_state": (
        ":reachable (rch err)",
        ["BMC"],
        "sat",
        [("main::x", "4"), ("main::err", "true"), ("rch", "true")],
    ),
    # The initial state itself
    "initial_state": (
        ":reachable (rch (= x 0))",
        ["BMC"],
        "sat",
        [("main::x", "0"), ("rch", "true")],
    ),
    # A condition over the current and next state: the state that starts
    # the transition is reported with the condition, the next one after it
    "two_state": (
        ":reachable (rch (and (= x 2) (= x' 3)))",
        ["BMC"],
        "sat",
        [("main::x", "3")],
    ),
    # A one-state assumption holds in the state the condition is checked in
    "one_state_assumption": (
        ":assumption (asm (< x 2)) :reachable (rch (= x 2))",
        ["BMC", "IND"],
        "unsat",
        [],
    ),
}


@pytest.mark.parametrize("case", cases, ids=cases)
def test_query_evaluated_in_its_state(tmp_path, case):
    if not kmoxi_bin.exists():
        pytest.skip(f"{kmoxi_bin} is not built (make kmoxi)")

    attrs, engines, expected, last_state = cases[case]
    names = " ".join(re.findall(r":(?:assumption|reachable) \((\w+)", attrs))
    path = tmp_path / f"{case}.moxi"
    path.write_text(
        system
        + f"(check-system main :input () :output ((x Int) (err Bool)) :local ()"
        f" {attrs} :query (q ({names})))\n"
    )
    args = common_args | {"--timeout": "30"}
    arg_list = [arg for pair in args.items() for arg in pair]
    enable = [arg for engine in engines for arg in ("--enable", engine)]
    popen_args = {} if os.name == "nt" else {"start_new_session": True}
    proc = subprocess.Popen(
        [kmoxi_bin, *arg_list, *enable, str(path)],
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
        **popen_args,
    )
    try:
        stdout, _ = proc.communicate(timeout=moxi_timeout)
    except subprocess.TimeoutExpired:
        kill_tree(proc)
        proc.communicate()
        pytest.fail(f"no answer after {moxi_timeout}s")
    output = re.sub(r"\x1b\[[0-9;]*m", "", stdout)
    assert f":query (q {expected}" in output, output

    if last_state:
        # The last step of the trail: its number, then (name value) pairs
        steps = re.findall(r"\((\d+) ((?:\([^()]*\)\s*)+)\)", output)
        assert steps, output
        _, values = steps[-1]
        for name, value in last_state:
            assert f"({name} {value})" in values, output
