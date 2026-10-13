"""IC3 with quantifier elimination extracts cubes from distinct terms.

The extraction of an implicant from a model, which IC3QE generalizes its
counterexamples to induction with, had no case for distinct and failed an
assertion on it: IC3QE stopped on every system whose formulas compare terms
with distinct, which MoXI models do. distinct is now the conjunction of the
disequalities of every two of its arguments, extracted from with the same
polarity.

Each model is checked with IC3QE alone, with the query reachable and not,
for distinct of two and of three arguments.
"""

import os
import re
import subprocess

import pytest

from conftest import kill_tree, kmoxi_args, kmoxi_bin

# Counters stepped by the given amounts from 0; the query asks for all of
# them to be pairwise distinct
def model(steps):
    names = "abc"[: len(steps)]
    vars_ = " ".join(f"({n} Int)" for n in names)
    init = " ".join(f"(= {n} 0)" for n in names)
    trans = " ".join(f"(= {n}' (+ {n} {d}))" for n, d in zip(names, steps))
    return f"""
(set-logic QF_LIA)
(define-system main :input () :output ({vars_}) :local ()
  :init (and {init}) :trans (and {trans}))
(check-system main :input () :output ({vars_}) :local ()
  :reachable (r (distinct {" ".join(names)})) :query (q (r)))
"""


cases = {
    # Distinct after one step
    "binary-sat": ([1, 2], "sat"),
    # Equal in every state
    "binary-unsat": ([1, 1], "unsat"),
    "ternary-sat": ([1, 2, 3], "sat"),
    # a and b are equal in every state
    "ternary-unsat": ([1, 1, 3], "unsat"),
}


@pytest.mark.parametrize("case", cases, ids=cases)
def test_ic3qe_distinct(tmp_path, case):
    if not kmoxi_bin.exists():
        pytest.skip(f"{kmoxi_bin} is not built (make kmoxi)")
    steps, expected = cases[case]
    path = tmp_path / f"{case}.moxi"
    path.write_text(model(steps))
    args = kmoxi_args | {"--timeout": "30"}
    arg_list = [arg for pair in args.items() for arg in pair]
    popen_args = {} if os.name == "nt" else {"start_new_session": True}
    proc = subprocess.Popen(
        [kmoxi_bin, "-v", *arg_list, "--enable", "IC3QE", str(path)],
        stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True, **popen_args,
    )
    try:
        stdout, stderr = proc.communicate(timeout=60)
    except subprocess.TimeoutExpired:
        kill_tree(proc)
        proc.communicate()
        pytest.fail("no answer after 60s")
    out = re.sub(r"\x1b\[[0-9;]*m", "", stdout + stderr)
    assert "Assertion failed" not in out, out
    assert f":query (q {expected}" in out, out
