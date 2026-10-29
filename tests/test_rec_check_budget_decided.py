"""The checks of the counterexamples of a round only take from their budget of
time when they leave their counterexample undecided.

A counterexample that reaches a recursive call past the unrollings is checked
against the functions as they are (see RecUnrolling), and the checks of a
round may take a few seconds in all. The time counted included that of the
checks that decided their counterexample, which is many times longer on a
loaded machine, as on the Windows runners of the CI (see #1867). The check of
the counterexample to "p", spurious, evaluates F at the call past the
unrollings, and then took the budget; the counterexample to the obligation of
the ascription one level down the recursion, which came after it and is
genuine, was left unchecked: with F at the limit of its unrollings, the
obligation was left unknown.

A wrapper stands in for a loaded machine: it waits 3 seconds before each
query of the solvers that evaluate the recursive functions, which are the
ones that take a resource limit, so that the evaluation of F, two queries,
takes more than the budget.
"""

import shutil
import sys

import pytest

from conftest import code_to_expected, common_args, kind2_bin, run_kind2

model = """
type Big = subtype { w: int | w >= 100 };

function G(n: int) returns (y: int);
let
  y = (n : Big);
tel

function rec F(n: int) returns (y: int);
con
  decreases n;
noc
let
  y = when n <= 0 then 0 else F(n - 1) + 0 * G(n);
tel

node N(x: int) returns ();
let
  assert x >= 100;
  check "p" F(x) >= 0;
tel
"""

wrapper_script = """#!{python}
import os, subprocess, sys, threading, time

z3 = subprocess.Popen([{z3!r}, *sys.argv[1:]], stdin=subprocess.PIPE)


def forward():
    slow = False
    # The end of the previous chunk, for a token split across two reads
    tail = b""
    try:
        while True:
            chunk = os.read(0, 65536)
            if not chunk:
                break
            text = tail + chunk
            tail = text[-16:]
            slow = slow or b":rlimit" in text
            if slow and b"check-sat" in text:
                time.sleep(3)
                # A command is not slowed down twice
                tail = b""
            z3.stdin.write(chunk)
            z3.stdin.flush()
        z3.stdin.close()
    except OSError:
        pass


# The solver is not always given commands: it is asked for its version too
threading.Thread(target=forward, daemon=True).start()
sys.exit(z3.wait())
"""

z3 = shutil.which("z3")


@pytest.mark.skipif(z3 is None, reason="needs z3")
@pytest.mark.skipif(
    sys.platform == "win32", reason="needs an executable script to slow Z3 down"
)
def test_genuine_counterexample_checked_after_slow_evaluation(tmp_path):
    wrapper = tmp_path / "z3"
    wrapper.write_text(wrapper_script.format(python=sys.executable, z3=z3))
    wrapper.chmod(0o755)
    path = tmp_path / "rec_check_budget_decided.lus"
    path.write_text(model)
    args = common_args | {"--timeout": "60"}
    arg_list = [arg for pair in args.items() for arg in pair]
    # The run is killed along with the wrapper and the solvers it starts if
    # it hangs
    run = run_kind2(
        [
            kind2_bin,
            *arg_list,
            "--smt_solver", "Z3",
            "--z3_bin", str(wrapper),
            # The spurious counterexample to "p" comes before the genuine
            # one with these engines
            "--enable", "BMC",
            "--enable", "IND",
            str(path),
        ]
    )
    output = run.stdout.decode() + run.stderr.decode()
    assert code_to_expected.get(run.returncode) == "falsifiable", output
    assert (
        "F[L20C13].F[L14C31].G[L14C46].TypeAscription[L6C7]: invalid"
        in run.stdout.decode()
    ), output
