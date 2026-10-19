"""kmoxi gives every check-system its response when time runs out.

When the time limit is reached, the engines are stopped, and every
check-system gets its response: the one being analyzed with what the
engines established, the ones not reached yet with every query unknown, as
the MoXI language definition gives for timeouts. kmoxi used to print
nothing when an engine was still running.

The time limit holds for the whole run: a check answered before it does
not stop the clock for the checks after it.
"""

import re
import time

import pytest

from conftest import LustreTimeout, kmoxi_args, kmoxi_bin, kmoxi_slack, run_kind2

# How long kmoxi runs, and how long it may take past it to stop and print
limit = 3
teardown = 15

systems = """(set-logic QF_LIA)
(define-system a :input ((i Int)) :output ((n Int)) :local ()
  :init (= n 0) :trans (= n' (+ n (ite (> i' 0) 2 0))))
"""


# n is even: BMC alone answers whether it can be 4, never whether it can be 3
def check(query, value):
    return (
        "(check-system a :input ((i Int)) :output ((n Int)) :local ()\n"
        f"  :reachable (r (= n {value})) :query ({query} (r)))\n"
    )


def run(tmp_path, model):
    if not kmoxi_bin.exists():
        pytest.skip(f"{kmoxi_bin} is not built (make kmoxi)")
    path = tmp_path / "model.moxi"
    path.write_text(model)
    args = kmoxi_args | {"--timeout": str(limit)}
    arg_list = [arg for pair in args.items() for arg in pair]
    start = time.monotonic()
    try:
        res = run_kind2([kmoxi_bin, *arg_list, "--enable", "BMC", path],
                        timeout=limit + kmoxi_slack)
    except LustreTimeout as e:
        pytest.fail("kmoxi did not stop at its time limit:\n"
                    + e.output.decode("utf-8", errors="replace"))
    elapsed = time.monotonic() - start
    out = res.stdout.decode("utf-8", errors="replace")
    assert res.returncode == 0, out
    assert elapsed < limit + teardown, f"{elapsed:.1f}s\n{out}"
    return re.findall(r":query \((\w+) :result (\w+)", out), out


@pytest.mark.parametrize("checks, answers", [
    # The check being analyzed
    ([("q", 3)], [("q", "unknown")]),
    # A check after an answered one
    ([("q1", 4), ("q", 3)], [("q1", "sat"), ("q", "unknown")]),
    # A check not reached
    ([("q", 3), ("q2", 4)], [("q", "unknown"), ("q2", "unknown")]),
], ids=["analyzed", "after-answered", "not-reached"])
def test_responses_on_timeout(tmp_path, checks, answers):
    model = systems + "".join(check(q, v) for q, v in checks)
    found, out = run(tmp_path, model)
    assert found == answers, out
    assert out.count("(check-system-response") == len(checks), out
