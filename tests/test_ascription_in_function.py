"""A type ascription in a function is generated as a function.

A type ascription (e : T) is desugared into a call to a generated component
whose input is of type T, so that T yields a proof obligation on e. It was
always generated as a node. A function that calls a node is not definable at
the SMT level (see LustreFunDefs), and neither is a recursive function that
calls it, directly or through other functions. The supervisor then has no
definition to check a counterexample that reaches a recursive call past the
unrollings with, and the obligation of the ascription in the recursive calls
was left unknown, even when it is violated.

In a function, the ascription is now generated as a function, and the
recursive function stays definable. An ascription whose type has a temporal
operator or a node call is still generated as a node, for the type checker
to reject it as before.
"""

import json
import subprocess

import pytest

from conftest import common_args, kind2_bin, run_timeout

# The ascription is in a function the recursive function calls
helper = """
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
"""

# The ascription is in the recursive function itself
direct = """
type Big = subtype { w: int | w >= 100 };

function rec F(n: int) returns (y: int);
con
  decreases n;
noc
let
  y = when n <= 0 then 0 else F(n - 1) + 0 * (n : Big);
tel
"""

# Any argument violates the ascription: at the call itself for x < 100, and
# down the recursion otherwise
any_argument = """
node N(x: int) returns ();
let
  check "p" F(x) = x;
tel
"""

# The ascription holds at the call, and is violated one level down the
# recursion, at n = 99
deeper = """
node N(x: int) returns ();
let
  assert x >= 100;
  check "p" F(x) >= 0;
tel
"""


def run(tmp_path, model, options):
    path = tmp_path / "ascription_in_function.lus"
    path.write_text(model)
    args = common_args | {"--timeout": "60"} | options
    arg_list = [arg for pair in args.items() for arg in pair]
    proc = subprocess.run(
        [kind2_bin, "-json", *arg_list, str(path)],
        capture_output=True,
        text=True,
        timeout=run_timeout,
    )
    objs = json.loads(proc.stdout)
    logs = [obj for obj in objs if obj.get("objectType") == "log"]
    errors = [
        log["value"] for log in logs if log.get("level") in ("error", "fatal")
    ]
    assert errors == [], errors
    ascriptions = [
        obj["answer"]["value"]
        for obj in objs
        if obj.get("objectType") == "property"
        and "type_ascription" in obj["name"]
    ]
    return logs, ascriptions


@pytest.mark.parametrize("function", [helper, direct], ids=["helper", "direct"])
def test_ascription_decided(tmp_path, function):
    logs, ascriptions = run(tmp_path, function + any_argument, {})
    # No counterexample is left at a recursive call that cannot be checked
    assert not any(
        "Counterexamples reach a recursive call" in log["value"] for log in logs
    ), logs
    assert ascriptions, ascriptions
    assert "unknown" not in ascriptions, ascriptions
    assert "falsifiable" in ascriptions, ascriptions


@pytest.mark.parametrize("function", [helper, direct], ids=["helper", "direct"])
@pytest.mark.parametrize(
    "options",
    [{}, {"--modular": "true", "--compositional": "true"}],
    ids=["default", "modular"],
)
def test_violation_down_the_recursion(tmp_path, function, options):
    _, ascriptions = run(tmp_path, function + deeper, options)
    assert "falsifiable" in ascriptions, ascriptions
