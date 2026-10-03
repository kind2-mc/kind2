"""A counterexample that reaches a call to a recursive function with an array
or map argument is checked without declaring the sort of arrays twice.

When the arrays are not the solver's (--smt_arrays false), they are of the
uninterpreted sort FArray, declared in the header of every solver script.
Checking whether a counterexample is spurious asked for the values of the
arguments of the calls past the unrollings, and the value of an array came
back as an opaque constant of FArray, such as FArray!val!0, which declared
FArray as an abstract type. Every solver started afterwards declared it a
second time, with no parameters, and the solver rejected the script: BMC,
the inductive step, k-induction, IC3 and the invariant generators all failed,
and the property was left unknown even with enough unrollings to prove it.
"""

import json
import subprocess

import pytest

from conftest import common_args, kind2_bin, run_timeout

array_model = """
function rec Sum(a: int^3; n: int) returns (r: int);
con decreases n; noc
let
  r = when n <= 0 or n > 3 then 0 else Sum(a, n - 1) + a[n - 1];
tel

node Test(b: int^3) returns ();
let
  check "sum3" Sum(b, 3) = b[0] + b[1] + b[2];
tel
"""

map_model = """
type Nat = subrange [0,*] of int;

function U() returns (r: Nat);
let
  r = 0;
tel

function rec G(n: Nat; m: map<int, int>) returns (ok: bool);
con
  guarantee "g" U() = 0;
  decreases n;
noc
let
  ok = when n > 0 then G(n - 1, m) else true;
tel
"""


def run(tmp_path, model, options):
    path = tmp_path / "model.lus"
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
    errors = [
        obj["value"]
        for obj in objs
        if obj.get("objectType") == "log"
        and obj.get("level") in ("error", "fatal")
    ]
    answers = {
        obj["name"]: obj["answer"]["value"]
        for obj in objs
        if obj.get("objectType") == "property"
    }
    return errors, answers


@pytest.mark.parametrize("arrays", ["false", "true"])
def test_array_argument_no_solver_errors(tmp_path, arrays):
    errors, answers = run(tmp_path, array_model, {"--smt_arrays": arrays})
    assert errors == [], errors
    assert answers.get("sum3") != "falsifiable", answers


@pytest.mark.parametrize("arrays", ["false", "true"])
def test_array_argument_proved_with_enough_unrollings(tmp_path, arrays):
    errors, answers = run(
        tmp_path,
        array_model,
        {"--smt_arrays": arrays, "--rec_unrollings": "4"},
    )
    assert errors == [], errors
    assert answers.get("sum3") == "valid", answers


@pytest.mark.parametrize("arrays", ["false", "true"])
def test_map_argument_refinement(tmp_path, arrays):
    errors, answers = run(
        tmp_path,
        map_model,
        {"--modular": "true", "--compositional": "true", "--smt_arrays": arrays},
    )
    assert errors == [], errors
    assert answers.get("g") == "valid", answers
