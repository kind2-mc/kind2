"""An expression moved out from under an arrow must be well defined at the
initial instant.

A 'pre' in the right operand of an arrow is left bare by the normalization,
since the arrow supplies the initial instant. That holds only while the
expression stays under the arrow: a pass that moves it out -- a hoisted lazy
guard, a restart condition, the local abstracting the scrutinee of a selector
-- leaves a reference to the instant before the first one, and the solver
rejects the query. Each model below reaches one of those passes; none may
produce a solver failure.
"""

import subprocess

import pytest

from conftest import common_args, kind2_bin, run_timeout

# A selector whose scrutinee is read through a 'pre': the local abstracting
# the scrutinee is defined outside the arrow
selector = """
datatype D = A (v: int) | B;
node main(i: int) returns (ok: bool);
var d: D;
let
  d = A(i);
  ok = true -> ((pre d).v = pre i);
  check ok;
tel
"""

# Same, for a recursive datatype, which keeps its selectors in the SMT encoding
recursive_selector = """
datatype List = Nil | Cons (hd: int, tl: List);
node main(i: int) returns (ok: bool);
var x: List;
let
  x = Cons(i, Nil);
  ok = true -> ((pre x).hd = pre i);
  check ok;
tel
"""

# A lazy guard is hoisted into a local defining the clock of the call it gates
lazy_guard = """
node Sum(v: int) returns (s: int);
let s = v -> pre s + v; tel

node main(a: int; b: bool) returns (ok: bool);
let
  ok = true -> (when (pre b) then Sum(a) > 0 else true);
  check ok;
tel
"""

# A restart condition is hoisted into a local holding the instance's reset flag
restart_condition = """
node cnt(i: int) returns (c: int);
let c = 0 -> pre c + i; tel

node main(i: int; r: bool) returns (ok: bool);
var o: int;
let
  o = 0 -> restart cnt(i) every (pre r);
  ok = i > 0 => o >= 0;
  check ok;
tel
"""

models = {
    "selector": selector,
    "recursive_selector": recursive_selector,
    "lazy_guard": lazy_guard,
    "restart_condition": restart_condition,
}


@pytest.mark.parametrize("name", sorted(models))
def test_no_solver_failure(tmp_path, name):
    path = tmp_path / "model.lus"
    path.write_text(models[name])
    args = common_args | {"--timeout": "20"}
    arg_list = [arg for pair in args.items() for arg in pair]
    proc = subprocess.run(
        [kind2_bin, *arg_list, str(path)],
        capture_output=True,
        text=True,
        timeout=run_timeout,
    )
    output = proc.stdout + proc.stderr
    assert "unknown constant" not in output, output
    assert "Runtime failure" not in output, output
