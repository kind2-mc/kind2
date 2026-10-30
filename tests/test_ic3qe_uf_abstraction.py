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

# A value of the function is buffered for a step before it is added: the
# property is not inductive, and its proof needs the invariant that the
# buffer is nonnegative, which IC3QE finds by generalizing through the
# application of the function, the path the other models do not take
buffered = imported + """
node main(x: int) returns (z: int);
var stage: bool; buf: int;
let
  stage = false -> not pre stage;
  buf = 0 -> if not pre stage then f(x) else pre buf;
  z = 0 -> if pre stage then pre z + pre buf else pre z;
  check "prop" z >= 0;
tel
"""

# The same with a buffer that may be negative: falsified two steps in, by a
# counterexample built from a generalized cube and checked on the system
buffered_falsified = imported + """
node main(x: int) returns (z: int);
var stage: bool; buf: int;
let
  stage = false -> not pre stage;
  buf = 0 -> if not pre stage then f(x) - 1 else pre buf;
  z = 0 -> if pre stage then pre z + pre buf else pre z;
  check "prop" z >= 0;
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


# A function without inputs, abstracted by its contract: its output is an
# application of a symbol to no argument, a constant in the terms
nullary = """
type Nat = subrange [0,*] of int;

function U() returns (r: Nat);
let
  r = 0;
tel

node G() returns (x: int);
let
  x = U() -> pre x + 2;
  check "prop" x <> 1;
tel
"""


# A selector of a datatype, partial: the generalization abstracts its
# applications like those of any other function symbol. The quantifier
# elimination of the solver, rather than Cooper's, used to fail on the fresh
# variables, which are not instances of state variables (#1879).
selector = """
datatype D = A (v: int) | B;
node main(i: int) returns (ok: bool);
var d: D;
let
  d = A(i);
  ok = true -> ((pre d).v = pre i);
  check "prop" ok;
tel
"""


def run_ic3qe(tmp_path, model, extra={}):
    path = tmp_path / "model.lus"
    path.write_text(model)
    args = common_args | {"--timeout": "30"} | extra
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
    assert "Runtime error" not in output, output
    assert "Assertion failed" not in output, output
    assert "system includes an abstract function" not in output, output
    return output


@pytest.mark.parametrize(
    "model", [accumulated, same_step, buffered, recursive],
    ids=["accumulated", "same_step", "buffered", "recursive"])
def test_proved(tmp_path, model):
    output = run_ic3qe(tmp_path, model)
    assert "Property prop is valid by property directed reachability (QE)" \
        in output, output


@pytest.mark.parametrize(
    "model", [falsified, buffered_falsified],
    ids=["falsified", "buffered_falsified"])
def test_falsified(tmp_path, model):
    output = run_ic3qe(tmp_path, model)
    assert "Property prop is invalid by property directed reachability (QE)" \
        in output, output


def test_spurious_counterexample_not_reported(tmp_path):
    output = run_ic3qe(tmp_path, cross_step)
    assert "is invalid" not in output, output
    assert "IC3QE stops: the counterexample found is spurious" in output, output


def test_nullary_application(tmp_path):
    output = run_ic3qe(tmp_path, nullary,
                       {"--modular": "true", "--compositional": "true"})
    assert "Property prop is invalid" not in output, output


# Without check-sat-assuming, which Kind 2 turns off for some solvers, the
# check runs in a push and pop, and its model is gone once it returns: the
# values of the applications are read with the model of the variables
@pytest.mark.parametrize(
    "model, answer",
    [(buffered, "valid"), (buffered_falsified, "invalid")],
    ids=["buffered", "buffered_falsified"])
def test_without_check_sat_assuming(tmp_path, model, answer):
    output = run_ic3qe(tmp_path, model, {"--check_sat_assume": "false"})
    assert f"Property prop is {answer} by property directed reachability (QE)" \
        in output, output


@pytest.mark.parametrize(
    "qe_method", [None, "precise", "impl", "impl2"],
    ids=["default", "precise", "impl", "impl2"])
def test_selector(tmp_path, qe_method):
    extra = {} if qe_method is None else {"--qe_method": qe_method}
    output = run_ic3qe(tmp_path, selector, extra)
    assert "Property prop is valid by property directed reachability (QE)" \
        in output, output
