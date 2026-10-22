"""A type ascription does not keep a function from being defined.

A type ascription (e : T) is desugared into a call to a generated node whose
input is of type T, so that T yields a proof obligation on e. A function
that calls a node was not definable at the SMT level (see LustreFunDefs), and
neither was a recursive function that calls it, directly or through other
functions, or whose contract does. The supervisor then had no definition to
check a counterexample that reaches a recursive call past the unrollings
with, and the obligation of the ascription in the recursive calls was left
unknown, even when it is violated.

In a definition, a call to an ascription node is now the identity on e: the
obligation is an assumption of the node, which the transition system keeps
checking at every call. The ascription is still generated as a node, so that
it is checked the same way in a function, in a node and in a contract,
whatever imports the contract, and it is inlined as before, in a decreases
measure for instance.
"""

import json
import subprocess

import pytest

from conftest import code_to_expected, common_args, kind2_bin, run_timeout

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

# The ascription is in a contract the recursive function imports
contract = """
type Big = subtype { w: int | w >= 100 };

contract C(n: int) returns (y: int);
let
  guarantee (n : Big) = n;
tel

function rec F(n: int) returns (y: int);
con
  import C(n) returns (y);
  decreases n;
noc
let
  y = when n <= 0 then 0 else F(n - 1);
tel
"""

functions = [helper, direct, contract]
function_ids = ["helper", "direct", "contract"]

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


def run(tmp_path, model, options={}):
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
    expected = code_to_expected.get(proc.returncode)
    assert expected in ("success", "falsifiable", "timeout"), (
        proc.returncode,
        proc.stdout,
        proc.stderr,
    )
    objs = json.loads(proc.stdout)
    logs = [obj for obj in objs if obj.get("objectType") == "log"]
    errors = [
        log["value"] for log in logs if log.get("level") in ("error", "fatal")
    ]
    assert errors == [], errors
    properties = [obj for obj in objs if obj.get("objectType") == "property"]
    return logs, properties


def ascriptions(properties):
    """The verdicts of the obligations of the ascription: the models have no
    other assumption to check"""
    return [
        prop["answer"]["value"]
        for prop in properties
        if prop.get("source") == "Assumption"
    ]


def unrolling_limit_reached(logs):
    return any(
        "Counterexamples reach a recursive call" in log["value"] for log in logs
    )


@pytest.mark.parametrize("function", functions, ids=function_ids)
def test_ascription_decided(tmp_path, function):
    logs, properties = run(tmp_path, function + any_argument)
    # No counterexample is left at a recursive call that cannot be checked
    assert not unrolling_limit_reached(logs), logs
    verdicts = ascriptions(properties)
    assert verdicts, properties
    assert "unknown" not in verdicts, properties
    assert "falsifiable" in verdicts, properties


@pytest.mark.parametrize("function", functions, ids=function_ids)
@pytest.mark.parametrize(
    "options",
    [{}, {"--modular": "true", "--compositional": "true"}],
    ids=["default", "modular"],
)
def test_violation_down_the_recursion(tmp_path, function, options):
    # "p" holds, but proving it takes an induction over the recursion, which
    # the unrollings do not give: it is left unknown, and its counterexamples
    # reach the unrolling limit
    _, properties = run(tmp_path, function + deeper, options)
    verdicts = ascriptions(properties)
    # The obligation holds at the call, and fails in the recursive call
    assert "valid" in verdicts, properties
    assert "falsifiable" in verdicts, properties


# An ascription to an array type is inlinable, and so is a function with one,
# as a decreases measure must be
measures = [
    "(a : int^2)[0]",
    "M(a)",
]


@pytest.mark.parametrize("measure", measures, ids=["ascription", "function"])
def test_ascription_in_decreases_measure(tmp_path, measure):
    model = f"""
function M(a: int^2) returns (y: int);
let
  y = (a : int^2)[0];
tel

function rec F(a: int^2) returns (y: int);
con
  decreases {measure};
noc
let
  y = when a[0] <= 0 then 0 else F([a[0] - 1, a[1]]);
tel
"""
    _, properties = run(tmp_path, model)
    checks = {
        prop["name"]: prop["answer"]["value"]
        for prop in properties
        if prop["name"].startswith("decrease_check")
    }
    assert list(checks.values()) == ["valid"], properties
