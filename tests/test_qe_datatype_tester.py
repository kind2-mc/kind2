"""A term the SMT solver gives back from a quantifier elimination over a
recursive datatype is read back into a term (see #1561).

Z3 eliminates a variable of a recursive datatype with constructor testers,
((_ is Cons) x), and selectors, (Cons_0 x), and the conversion of its result
into a term had a case for neither: the tester fell through to "Invalid
S-expression", and a selector is not declared as an uninterpreted function.
Both the contract checker, whose realizability check eliminates the outputs,
and IC3 with quantifier elimination stopped on a runtime failure.

Each model is checked by the engine that eliminates quantifiers alone, so that
no other engine settles the properties first.
"""

import json
import subprocess

import pytest

from conftest import common_args, kind2_bin, run_timeout

# A tester in an assumption: the realizability check of the contract
contract = """
datatype List = Nil | Cons (hd: int, tl: List);

node imported f(x: List) returns (y: bool);
(*@contract
  assume Cons?(x);
  guarantee y;
*)

node main() returns ();
let
tel
"""

# A selector read through a 'pre': IC3QE generalizes over the previous value
# of the list, a Cons whose head and tail it eliminates
selector = """
datatype List = Nil | Cons (hd: int, tl: List);
node main(i: int) returns (ok: bool);
var x, y: List;
let
  x = Cons(i, Nil);
  y = Nil -> pre x;
  ok = true -> (y.hd = pre i);
  check ok;
tel
"""

# The model, the engine, and the answer of each of its properties or contracts
cases = {
    "contract": (contract, "CONTRACTCK", "realizabilityCheck", {
        "List type": "realizable",
        "f environment": "realizable",
        "f contract": "realizable",
        "main contract": "realizable",
        "main environment": "realizable",
    }),
    "selector": (selector, "IC3QE", "property", {
        "InvProp[L9C3]": "valid",
        "Selector[L8C18]": "falsifiable",
    }),
}


@pytest.mark.parametrize("case", sorted(cases))
def test_qe_datatype_tester(tmp_path, case):
    model, engine, kind, expected = cases[case]
    path = tmp_path / "model.lus"
    path.write_text(model)
    arg_list = [arg for pair in common_args.items() for arg in pair]
    proc = subprocess.run(
        [kind2_bin, "-json", *arg_list, "--enable", engine, str(path)],
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
    if kind == "property":
        answers = {
            obj["name"]: obj["answer"]["value"]
            for obj in objs
            if obj.get("objectType") == "property"
        }
    else:
        # A realizability check reports in the analysis of a node, by context
        answers, analysis = {}, None
        for obj in objs:
            if obj.get("objectType") == "analysisStart":
                analysis = f'{obj["top"]} {obj["context"]}'
            elif obj.get("objectType") == kind:
                answers[analysis] = obj["result"]
    assert answers == expected, proc.stdout
