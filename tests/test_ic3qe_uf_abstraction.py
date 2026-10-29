"""IC3QE on systems with function symbols.

The quantifier elimination of IC3QE's generalization does not reason about
function symbols, so IC3QE used to shut down on any system with an abstract
function (an imported function, a function abstracted by its contract, ...)
or a recursive function defined at the SMT level. The generalization now
works on an abstraction of the system: each shape of application of such
a symbol, f(t), has an application variable a, with a' = f(t') after each
transition, a = f(t) in the initial states and the congruence of the
application variables of a symbol (equal arguments give equal values). The
checks of IC3QE keep the symbols, so its proofs hold of the system. The
abstraction relates the applications of one state and the next only, so a
counterexample of the abstraction may interpret a symbol differently at
different steps: the counterexample is checked on the system, and when it
is spurious the abstraction is refined with history variables, which carry
the arguments and the value of an application to the later steps, and
IC3QE restarts; --ic3qe_uf_refinements bounds the refinements.
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

# Equal arguments two steps apart give equal values: the abstraction does
# not relate the applications of different steps, so the counterexample
# IC3QE first finds is spurious; a refinement with a history of two steps
# proves the property
cross_step = imported + """
node main(x: int) returns (ok: bool);
var n: int;
let
  n = 0 -> if pre n < 2 then pre n + 1 else 2;
  ok = n < 2 or (x = pre pre x => f(x) = pre pre f(x));
  check "prop" ok;
tel
"""

# The same, three steps apart
cross_step_3 = imported + """
node main(x: int) returns (ok: bool);
var n: int;
let
  n = 0 -> if pre n < 3 then pre n + 1 else 3;
  ok = n < 3 or (x = pre pre pre x => f(x) = pre pre pre f(x));
  check "prop" ok;
tel
"""

# The value of the function on a constant is added twice: the sum is twice
# the value, as the application two steps later has the same arguments
constant_sum = imported + """
node main(c: int) returns (z: int; k: int);
var x: int;
let
  x = c -> pre x;
  k = 0 -> if pre k < 2 then pre k + 1 else 2;
  z = 0 -> if pre k < 2 then pre z + f(x) else pre z;
  check "prop" k = 2 => z = 2 * f(x);
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


def run_ic3qe(tmp_path, model, extra={}, flags=[]):
    path = tmp_path / "model.lus"
    path.write_text(model)
    args = common_args | {"--timeout": "30"} | extra
    arg_list = [arg for pair in args.items() for arg in pair]
    run = subprocess.run(
        [kind2_bin, *arg_list, *flags, "--enable", "IC3QE", str(path)],
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
    "model",
    [accumulated, same_step, buffered, recursive,
     cross_step, cross_step_3, constant_sum],
    ids=["accumulated", "same_step", "buffered", "recursive",
         "cross_step", "cross_step_3", "constant_sum"])
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


# The proofs of the cross-step models go through a refinement
@pytest.mark.parametrize(
    "model", [cross_step, cross_step_3, constant_sum],
    ids=["cross_step", "cross_step_3", "constant_sum"])
def test_refined(tmp_path, model):
    output = run_ic3qe(tmp_path, model, flags=["-v"])
    assert "refining the abstraction of the function symbols with history " \
        "variables (1 of 20 refinements)" in output, output
    assert "Property prop is valid by property directed reachability (QE)" \
        in output, output


# Without refinements, the spurious counterexample is detected and IC3QE
# stops, without reporting it
def test_spurious_counterexample_not_reported(tmp_path):
    output = run_ic3qe(tmp_path, cross_step, {"--ic3qe_uf_refinements": "0"})
    assert "is invalid" not in output, output
    assert "IC3QE stops: the counterexample found is spurious" in output, output


def test_nullary_application(tmp_path):
    output = run_ic3qe(tmp_path, nullary,
                       {"--modular": "true", "--compositional": "true"})
    assert "Property prop is invalid" not in output, output


# Without check-sat-assuming, which Kind 2 turns off for some solvers, the
# checks run in a push and pop
@pytest.mark.parametrize(
    "model, answer",
    [(buffered, "valid"), (buffered_falsified, "invalid"),
     (cross_step, "valid")],
    ids=["buffered", "buffered_falsified", "cross_step"])
def test_without_check_sat_assuming(tmp_path, model, answer):
    output = run_ic3qe(tmp_path, model, {"--check_sat_assume": "false"})
    assert f"Property prop is {answer} by property directed reachability (QE)" \
        in output, output


# The variables of the abstraction are declared in the solver of the
# quantifier elimination too, when the generalization uses one
def test_solver_qe(tmp_path):
    output = run_ic3qe(tmp_path, cross_step, {"--qe_method": "impl"})
    assert "Property prop is valid by property directed reachability (QE)" \
        in output, output
