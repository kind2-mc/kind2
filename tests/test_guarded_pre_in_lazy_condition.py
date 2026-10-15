"""A 'pre' guarded by '->' in a condition abstracted into a local of its own.

The guard of a lazy construct whose guarded operand is temporal, the condition
of a restart, and the guards of a selector obligation are abstracted into
locals, or into the definition of the obligation, outside of the '->' that
guards their 'pre'. They were defined at the initial state too, where the 'pre'
refers to offset -1, and the solver rejected the queries with an unknown
constant. The other engines prove the properties of the issue, so BMC runs
alone, on properties it can falsify: it reports each of them falsifiable
rather than failing (see #1744).

A guard is false at the initial state, so the call it activates first runs at
the first later step where the guard holds. The length of each counterexample
pins this down: with the guard true at the initial state instead, the
properties would fail one step earlier.
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
        "==>": 3,
        "and then": 1,
        "or else": 3,
        "when": 3,
        "restart": 2,
    }),
    "selector": (selector_model, {
        "selector": 1,
        "Selector[L5C40]": 1,
    }),
    "shifted_selector": (shifted_selector_model, {
        "selector": 2,
        "Selector[L5C53]": 2,
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
