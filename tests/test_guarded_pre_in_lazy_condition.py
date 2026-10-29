"""A 'pre' guarded by '->' in a condition abstracted into a local of its own.

The guard of a lazy construct whose guarded operand is temporal, the condition
of a restart, and the guards of a selector obligation are abstracted into
locals, or into the definition of the obligation, outside of the '->' that
guards their 'pre'. They are defined at the initial state too, where the 'pre'
refers to offset -1, so each of them supplies its own initial instant with an
oracle, as a node-call argument always has. BMC runs alone here, on properties
it can falsify, so none of the queries may be rejected with an unknown
constant (see #1744, #1562).

An oracle is unconstrained, so a guard may hold at the initial state: a call
the guard activates may already run there. The length of each counterexample
pins this down -- wherever the guard gates a stateful call, the property fails
one step earlier than it would if the guard were false at the initial state.
"""

import json
import subprocess

import pytest

from conftest import common_args, kind2_bin, run_timeout

lazy_model = """
node Count() returns (n: int);
let
  n = 1 -> pre n + 1;
tel

node main(c: bool) returns ();
let
  check "==>" true -> (not pre c ==> Count() < 3);
  check "and then" true -> (pre c and then Count() >= 3);
  check "or else" true -> (pre c or else Count() < 3);
  check "when" true -> (when not pre c then Count() < 3 else true);
  check "restart" (0 -> (restart Count() every pre c)) < 3;
tel
"""

selector_model = """
datatype IntOpt = None | Some (val: int);
node main(c: bool; x: IntOpt) returns ();
let
  check "selector" true -> (pre c ==> x.val > 0);
tel
"""

shifted_selector_model = """
datatype IntOpt = None | Some (val: int);
node main(c: bool; x: IntOpt) returns ();
let
  check "selector" true -> pre (true -> (pre c ==> x.val > 0));
tel
"""

# The model, and the length of the counterexample of each of its properties
cases = {
    "lazy": (lazy_model, {
        "==>": 2,
        "and then": 1,
        "or else": 2,
        "when": 2,
        "restart": 2,
    }),
    "selector": (selector_model, {
        "selector": 1,
        "Selector[L5C40]": 0,
    }),
    "shifted_selector": (shifted_selector_model, {
        "selector": 2,
        "Selector[L5C53]": 1,
    }),
}


@pytest.mark.parametrize("case", cases)
def test_guarded_pre_in_lazy_condition(tmp_path, case):
    model, expected = cases[case]
    path = tmp_path / "model.lus"
    path.write_text(model)
    args = common_args | {"--timeout": "30", "--enable": "BMC"}
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
        if obj.get("objectType") == "log" and obj.get("level") == "error"
    ]
    assert errors == [], errors
    answers = {
        obj["name"]: (obj["answer"]["value"], obj.get("k"))
        for obj in objs
        if obj.get("objectType") == "property"
    }
    assert answers == {p: ("falsifiable", k) for p, k in expected.items()}, answers
