"""IC3QE on systems with function symbols.

The quantifier elimination of IC3QE's generalization does not reason about
function symbols, so IC3QE used to shut down on any system with an abstract
function (an imported function, a function abstracted by its contract, ...)
or a recursive function defined at the SMT level. The generalization now
replaces each application of such a symbol by a fresh variable, with the
Ackermann constraints of the applications of each symbol (equal arguments
give equal values), and eliminates the fresh variables with the primed
ones. The checks of IC3QE keep the symbols, so its proofs hold of the
system. A counterexample built from the generalized cubes may interpret a
symbol differently at different steps: it is checked as a whole on the
system, and IC3QE stops if it does not hold there.
"""

import subprocess

import pytest

from conftest import common_args, kind2_bin, run_timeout

imported = """
function imported f(x: int) returns (y: int);
(*@contract guarantee y >= 0; *)
"""

# A sum of values of the function, nonnegative by its contract
accumulated = imported + """
node main(x: int) returns (z: int);
let
  z = 0 -> pre z + f(x);
  check "prop" z >= 0;
tel
"""

# Two applications with equal arguments in the same step: equal values
same_step = imported + """
node main(x: int) returns (n: int);
var y: int;
let
  y = x;
  n = 0 -> pre n + (if f(x) = f(y) then 0 else 1);
  check "prop" n = 0;
tel
"""

# The function may return 0, so the sum may be 0
falsified = imported + """
node main(x: int) returns (z: int);
let
  z = 0 -> pre z + f(x);
  check "prop" z > 0;
tel
"""

# Equal arguments two steps apart give equal values: valid, but the
# generalization does not relate applications of different steps, so the
# counterexample IC3QE builds is spurious, and it must not report it
cross_step = imported + """
node main(x: int) returns (ok: bool);
var n: int;
let
  n = 0 -> if pre n < 2 then pre n + 1 else 2;
  ok = n < 2 or (x = pre pre x => f(x) = pre pre f(x));
  check "prop" ok;
tel
"""

# A recursive function, with calls within the default limit on unrollings
# (when, the lazy if, guards the recursive call)
recursive = """
function rec fact(n: int) returns (f: int)
con decreases n; noc
let
  f = when n <= 0 then 1 else n * fact(n - 1);
tel

node main(x: int) returns (z: int);
let
  z = fact(1) -> pre z + (when x > 0 then fact(1) else 0);
  check "prop" z >= 1;
tel
"""


def run_ic3qe(tmp_path, model):
    path = tmp_path / "model.lus"
    path.write_text(model)
    args = common_args | {"--timeout": "30"}
    arg_list = [arg for pair in args.items() for arg in pair]
    run = subprocess.run(
        [kind2_bin, *arg_list, "--enable", "IC3QE", str(path)],
        capture_output=True,
        text=True,
        timeout=run_timeout,
    )
    output = run.stdout + run.stderr
    assert "terminated on exception" not in output, output
    assert "Runtime failure" not in output, output
    assert "Assertion failed" not in output, output
    assert "system includes an abstract function" not in output, output
    return output


@pytest.mark.parametrize(
    "model", [accumulated, same_step, recursive],
    ids=["accumulated", "same_step", "recursive"])
def test_proved(tmp_path, model):
    output = run_ic3qe(tmp_path, model)
    assert "Property prop is valid by property directed reachability (QE)" \
        in output, output


def test_falsified(tmp_path):
    output = run_ic3qe(tmp_path, falsified)
    assert "Property prop is invalid by property directed reachability (QE)" \
        in output, output


def test_spurious_counterexample_not_reported(tmp_path):
    output = run_ic3qe(tmp_path, cross_step)
    assert "is invalid" not in output, output
    assert "IC3QE stops: the counterexample found is spurious" in output, output
