"""kmoxi answers each check-system of a script on its own.

The system kmoxi builds for a check-system used to be named "query" for
every check, so all of them had the same scope and the same variables. Each
analysis looked its system up by that scope, and found the same one: a
script with two checks got the response of one of them, twice. Each check
now has a system of its own, numbered, and the responses follow the order
of the script.
"""

import re
import subprocess

import pytest

from conftest import kill_tree, kmoxi_args, kmoxi_bin

system = """(set-logic QF_LIA)
(define-system main :input () :output ((x Int)) :local ((t Int))
  :init (and (= x 0) (= t 0)) :trans (and (= x' (+ x 2)) (= t' (+ t 1))))
"""


def check(condition, reachable, query):
    return (
        "(check-system main :input () :output ((x Int)) :local ((t Int))\n"
        f"  :reachable ({condition} {reachable}) :query ({query} ({condition})))\n"
    )


def run(tmp_path, model):
    if not kmoxi_bin.exists():
        pytest.skip(f"{kmoxi_bin} is not built (make kmoxi)")
    path = tmp_path / "model.moxi"
    path.write_text(model)
    args = kmoxi_args | {"--timeout": "30"}
    arg_list = [arg for pair in args.items() for arg in pair]
    proc = subprocess.Popen(
        [kmoxi_bin, *arg_list, "--enable", "BMC", "--enable", "IND", str(path)],
        stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True,
        start_new_session=True,
    )
    try:
        stdout, stderr = proc.communicate(timeout=60)
    except subprocess.TimeoutExpired:
        kill_tree(proc)
        proc.communicate()
        pytest.fail("no answer after 60s")
    return stdout + stderr


# The conditions of the two checks have the same name, or different ones:
# x is never negative, and is 4 after two steps
@pytest.mark.parametrize("second", ["r", "s"], ids=["same-name", "other-name"])
def test_each_check_answered(tmp_path, second):
    model = (system + check("r", "(< x 0)", "q1")
             + check(second, "(and (= t 2) (= x 4))", "q2"))
    out = run(tmp_path, model)
    answers = re.findall(r":query \((\w+) (\w+)", out)
    assert answers == [("q1", "unsat"), ("q2", "sat")], out
