"""The properties of a called node outside the cone of influence of the caller.

With node slicing, a call that nothing in the calling node depended on was
sliced away, and so were the proof obligations it carries into the calling
node. Which properties of the called nodes are checked is now up to
--check_subproperties alone, whatever the slicing (see #1752):

- with true, all of them;
- with relevant, those of the calls in the cone of influence of the
  properties of the top node, which is what node slicing used to check;
- with false, none.

The properties of a node Kind 2 generates for a part of the calling node,
such as the checks of the selectors in a temporal branch of a `when`
expression, are properties of the calling node, and the assumptions of the
contract of a called node are obligations of the calling node: they are
checked with every value.
"""

import json
import subprocess

import pytest

from conftest import common_args, kind2_bin, run_timeout

slicings = ["on", "off", "experimental"]

callee = """\
node Callee(x: int) returns (y: int);
let
  y = x;
  check "callee" y > 0;
tel

node main(x: int) returns (y: int);
let
  y = Callee(x);
  {prop}
tel
"""

# A property of main that does not depend on the output of the call, if any
unrelated_props = {
    "none": "",
    "trivial": "check true;",
    "self": "check y = y;",
    "input": "check x = x;",
}

# A node without properties that calls a node with one, a node with a
# contract, and a property of main that depends on neither
nested = """\
node Sub(x: int) returns (y: int);
let
  y = x;
  check "sub" y > 0;
tel

node Mid(x: int) returns (y: int);
var z: int;
let
  z = Sub(x);
  y = x;
tel

node Ctr(x: int) returns (y: int);
(*@contract assume x > 0; guarantee y > 1; *)
let
  y = x;
tel

node main(x: int) returns (y: int);
var a, b: int;
let
  a = Mid(x);
  b = Ctr(x);
  y = x;
  check true;
tel
"""

# The example of the issue, and the one of its last comment
selector = """\
datatype O = N | S (v: int);

node main(c: bool; s: O) returns (y: int);
let
  y = when c then (0 -> pre s.v) else 0;
  check y = y;
tel
"""

wrong_guard = """\
datatype O = N | S (v: int);

node main(x: O) returns (y: int);
let
  y = when N?(x) then (0 -> pre x.v) else 0;
  {prop}
tel
"""

# Two calls of a node with a generated node inside, only one of which the
# property of main depends on
two_calls = """\
datatype O = N | S (v: int);

node M(x: O) returns (y: int);
let
  y = when N?(x) then (0 -> pre x.v) else 0;
tel

node main(x: O) returns (z: int);
var u, w: int;
let
  u = M(x);
  w = M(x);
  z = 0;
  check z = 0 or w = w + 0;
tel
"""


def answers(tmp_path, model, subproperties, slicing):
    """The answers to the properties of the analysis of main"""
    path = tmp_path / "model.lus"
    path.write_text(model)
    args = common_args | {
        "--check_subproperties": subproperties,
        "--slice_nodes": slicing,
    }
    arg_list = [arg for pair in args.items() for arg in pair]
    proc = subprocess.run(
        [kind2_bin, "-json", *arg_list, str(path)],
        capture_output=True,
        text=True,
        timeout=run_timeout,
    )
    return {
        obj["name"]: obj["answer"]["value"]
        for obj in json.loads(proc.stdout)
        if obj.get("objectType") == "property"
    }


@pytest.mark.parametrize("slicing", slicings)
@pytest.mark.parametrize("prop", unrelated_props)
@pytest.mark.parametrize(
    "subproperties, checked",
    [("true", True), ("relevant", False), ("false", False)],
)
def test_callee_outside_coi(tmp_path, prop, subproperties, checked, slicing):
    model = callee.format(prop=unrelated_props[prop])
    result = answers(tmp_path, model, subproperties, slicing)
    assert ("Callee[L9C7].callee" in result) == checked, result
    if checked:
        assert result["Callee[L9C7].callee"] == "falsifiable", result


@pytest.mark.parametrize("slicing", slicings)
@pytest.mark.parametrize("subproperties", ["true", "relevant"])
def test_callee_in_coi(tmp_path, subproperties, slicing):
    model = callee.format(prop="check y = x;")
    result = answers(tmp_path, model, subproperties, slicing)
    assert result == {
        "InvProp[L10C3]": "valid",
        "Callee[L9C7].callee": "falsifiable",
    }, result


@pytest.mark.parametrize("slicing", slicings)
@pytest.mark.parametrize(
    "subproperties, expected",
    [
        (
            "true",
            {
                "InvProp[L26C3]": "valid",
                "Mid[L23C7].Sub[L10C7].sub": "falsifiable",
                "Ctr[L24C7].assume[L15C13]": "falsifiable",
                "Ctr[L24C7].guarantee[L15C27]": "falsifiable",
            },
        ),
        # The assumptions of a call are obligations of the caller, and depend
        # on the inputs of the call only: the guarantee is not relevant
        (
            "relevant",
            {
                "InvProp[L26C3]": "valid",
                "Ctr[L24C7].assume[L15C13]": "falsifiable",
            },
        ),
        (
            "false",
            {
                "InvProp[L26C3]": "valid",
                "Ctr[L24C7].assume[L15C13]": "falsifiable",
            },
        ),
    ],
)
def test_nested_and_contract(tmp_path, subproperties, expected, slicing):
    assert answers(tmp_path, nested, subproperties, slicing) == expected


@pytest.mark.parametrize("slicing", slicings)
@pytest.mark.parametrize("subproperties", ["true", "relevant", "false"])
def test_generated_node(tmp_path, subproperties, slicing):
    assert answers(tmp_path, selector, subproperties, slicing) == {
        "InvProp[L6C3]": "valid",
        "Selector[L5C30]": "falsifiable",
    }


@pytest.mark.parametrize("slicing", slicings)
@pytest.mark.parametrize("subproperties", ["true", "relevant", "false"])
@pytest.mark.parametrize("prop", ["", "check y = y;"])
def test_generated_node_wrong_guard(tmp_path, prop, subproperties, slicing):
    result = answers(
        tmp_path, wrong_guard.format(prop=prop), subproperties, slicing
    )
    assert result.get("Selector[L5C34]") == "falsifiable", result


@pytest.mark.parametrize("slicing", slicings)
@pytest.mark.parametrize(
    "subproperties, instances",
    [("true", ["L11C7", "L12C7"]), ("relevant", ["L12C7"]), ("false", [])],
)
def test_generated_node_of_callee(tmp_path, subproperties, instances, slicing):
    result = answers(tmp_path, two_calls, subproperties, slicing)
    assert result == {"InvProp[L14C3]": "valid"} | {
        f"M[{pos}].Selector[L5C34]": "falsifiable" for pos in instances
    }, result
