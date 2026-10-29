"""An expression moved out from under an arrow must be well defined at the
initial instant.

A 'pre' in the right operand of an arrow is left bare by the normalization,
since the arrow supplies the initial instant. That holds only while the
expression stays under the arrow: a pass that moves it out -- a hoisted lazy
clock, a restart condition, the local abstracting the scrutinee of a selector,
a selector proof obligation -- would leave a reference to the instant before
the first one, and the solver would reject the query. Each relocated expression
therefore supplies its own initial instant with an oracle, as a node-call
argument always has (see #1562).

An oracle is unconstrained, so a scrutinee relocated this way has an arbitrary
value at the initial instant: the obligation that its constructor is the one
the selector belongs to reports there. The verdicts below pin that down, so
that an obligation cannot regress into being vacuously valid.
"""

import json
import subprocess

import pytest

from conftest import common_args, kind2_bin, run_timeout

# A selector whose scrutinee is read through a 'pre': the local abstracting
# the scrutinee is defined outside the arrow, and takes an arbitrary value at
# the initial instant, where the constructor is not established
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

# An arrow inside the scrutinee gives it a value of its own at the initial
# instant, so no oracle is introduced and the constructor is established there
initialized_selector = """
datatype D = A (v: int) | B;
node main(i: int) returns (ok: bool);
var d: D;
let
  d = A(i);
  ok = true -> ((A(0) -> pre d).v = pre i);
  check ok;
tel
"""

# A selector in the clock of a lazy construct: the clock is hoisted into a
# local defining the clock of the call it gates, so the obligation holds
# wherever the clock is read, the initial instant included
lazy_clock = """
datatype D = A (v: int) | B;
node Count(c: bool) returns (n: int);
let n = (if c then 1 else 0) -> pre n; tel

node main() returns (ok: bool);
var p: D;
let
  p = B -> A(1);
  ok = true -> ((when p.v > 0 then Count(true) else 0) <= 1);
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

# The model, and the answer of each of its properties, with the length of the
# counterexample where there is one
cases = {
    "selector": (selector, {
        "InvProp[L8C3]": ("valid", None),
        "Selector[L7C24]": ("falsifiable", 0),
    }),
    "recursive_selector": (recursive_selector, {
        "InvProp[L8C3]": ("valid", None),
        "Selector[L7C24]": ("falsifiable", 0),
    }),
    "initialized_selector": (initialized_selector, {
        "InvProp[L8C3]": ("valid", None),
        "Selector[L7C32]": ("valid", None),
    }),
    "lazy_clock": (lazy_clock, {
        "InvProp[L11C3]": ("valid", None),
        "Selector[L10C24]": ("falsifiable", 0),
    }),
    "lazy_guard": (lazy_guard, {
        "InvProp[L8C3]": ("falsifiable", 1),
    }),
    "restart_condition": (restart_condition, {
        "InvProp[L10C3]": ("falsifiable", 2),
    }),
}


@pytest.mark.parametrize("case", sorted(cases))
def test_pre_under_arrow_well_defined(tmp_path, case):
    model, expected = cases[case]
    path = tmp_path / "model.lus"
    path.write_text(model)
    args = common_args | {"--timeout": "30"}
    arg_list = [arg for pair in args.items() for arg in pair]
    proc = subprocess.run(
        [kind2_bin, "-json", *arg_list, str(path)],
        capture_output=True,
        text=True,
        timeout=run_timeout,
    )
    objs = json.loads(proc.stdout)
    errors = [
        obj["value"]
        for obj in objs
        if obj.get("objectType") == "log" and obj.get("level") in ("error", "fatal")
    ]
    assert errors == [], errors
    answers = {
        obj["name"]: (obj["answer"]["value"], obj.get("k"))
        for obj in objs
        if obj.get("objectType") == "property"
    }
    assert answers == expected, answers
