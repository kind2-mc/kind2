"""A call applied to a variable whose type mentions an input of the node.

An inlined call, or a call compiled to an application of the functional symbol
of the callee, keeps a node instance whose arguments have the variables of the
enclosing quantifiers, or the index variable of a comprehension, replaced by
free constants. The constants used to be typed with the type of the variables,
whose range was asserted where only the global symbols are declared: a
refinement that mentions an input of the node, such as the index type
`int | 0 <= _ < n` of a comprehension of size `n`, made the engines that
assert it fail with an "unknown constant" solver error (issue #1820).

The constants are now of the base type, and the refinement gates the instance
instead, so that the obligations of the callee, such as the refinement of its
input, are still checked for exactly the values of the type: valid when the
type is within the refinement of the input, and invalid when it is not.
"""

import re

import pytest

from conftest import common_args, kind2_bin, run_kind2

models = {
    # A constant input, in a comprehension of unbounded size
    "comprehension-const": (
        """
function add (const n: int; k: int) returns (v: int);
let
  v = k + n;
tel

node main (const n: int) returns (A: int^n);
let
  A = (add(n, i) foreach i)^n;
  check "p" true;
tel
""",
        {"p": ["valid"]},
    ),
    # An array input, which BMC used to fail on as well
    "comprehension-array": (
        """
function get (p: int^3; k: int) returns (v: int);
let
  v = p[0];
tel

node main (const n: int; P: int^3) returns (A: int^n);
let
  A = (get(P, i) foreach i)^n;
  check "p" true;
tel
""",
        {"p": ["valid"]},
    ),
    # A quantified variable of a refinement type
    "quantifier": (
        """
function get (const n: int; p: int^n; k: int) returns (v: int);
let
  v = p[0];
tel

node main (const n: int; P: int^n) returns ();
let
  check "p" forall (k: int | 0 <= k and k < n) get(n, P, k) = P[0];
tel
""",
        {"p": ["valid"]},
    ),
    # The refinement of the input of the callee holds for the values of the
    # type of the variable
    "subtype-valid": (
        """
function inc (k: int | k >= 0) returns (v: int);
let
  v = k + 1;
tel

node main (const n: int) returns ();
let
  check "p" forall (k: int | k >= 0 and k < n) inc(k) > 0;
tel
""",
        {"p": ["valid"], "inc.SubType": ["valid"]},
    ),
    # ... and fails for one of them
    "subtype-invalid": (
        """
function inc (k: int | k >= 0) returns (v: int);
let
  v = k + 1;
tel

node main (const n: int) returns ();
let
  check "p" forall (k: int | k >= -1 and k < n) inc(k) > -5;
tel
""",
        {"p": ["valid"], "inc.SubType": ["invalid"]},
    ),
    # A variable the guard of a call depends on, and its arguments do not
    # mention
    "guard": (
        """
function inc (x: int | x >= 0) returns (v: int);
let
  v = x + 1;
tel

node main (const n: int; P: int^n) returns ();
let
  check "p" forall (k: int | 0 <= k and k < n)
    (when P[k] >= 0 then inc(P[k]) > 0 else true);
tel
""",
        {"p": ["valid"], "inc.SubType": ["valid"]},
    ),
    # A call in the arguments of a call applied to the variable is applied to
    # the constant that replaces the variable, and is gated by the type too
    "nested-valid": (
        """
function inc (x: int | x >= 0) returns (v: int);
let
  v = x + 1;
tel

node main (const n: int) returns ();
let
  check "p" forall (k: int | k >= 0 and k < n) inc(inc(k)) > 0;
tel
""",
        {"p": ["valid"], "inc.SubType": ["valid", "valid"]},
    ),
    # ... where the inner call fails for a value of the type, and the outer
    # one does not
    "nested-invalid": (
        """
function inc (x: int | x >= 0) returns (v: int);
let
  v = x + 1;
tel

node main (const n: int) returns ();
let
  check "p" forall (k: int | k >= -1 and k < n) inc(inc(k)) > 0;
tel
""",
        {"p": ["valid"], "inc.SubType": ["invalid", "valid"]},
    ),
    # Nested calls over the index variable of a comprehension, which used to
    # fail an assertion of the normalizer
    "nested-comprehension": (
        """
function f (x: int | x >= 1) returns (v: int);
let
  v = x + 1;
tel

function g (x: int) returns (v: int);
let
  v = x + 1;
tel

node main (const n: int) returns (A: int^n; B: int^n);
let
  A = (g(g(i)) foreach i)^n;
  B = (f(g(i)) foreach i)^n;
  check "p" true;
tel
""",
        {"p": ["valid"], "f.SubType": ["valid"]},
    ),
}


def summary(output):
    """The statuses of the properties in the summary of the run, by name
    without the source positions, sorted: two instances of a callee have
    properties of the same name"""
    by_full_name = {}
    for section in output.split("Summary of Properties")[1:]:
        for line in section.splitlines():
            name, sep, rest = line.partition(": ")
            if sep and rest and not line.startswith(" "):
                by_full_name[name] = rest.split()[0]
    statuses = {}
    for name, status in by_full_name.items():
        name = re.sub(r"\[L\d+C\d+\]", "", name)
        statuses.setdefault(name, []).append(status)
    return {name: sorted(s) for name, s in statuses.items()}


@pytest.mark.parametrize("name", list(models))
def test_no_solver_error(tmp_path, name):
    model, expected = models[name]
    path = tmp_path / "model.lus"
    path.write_text(model)
    args = common_args | {"--timeout": "30"}
    arg_list = [arg for pair in args.items() for arg in pair]
    proc = run_kind2([kind2_bin, *arg_list, str(path)])
    output = proc.stdout.decode("utf-8", errors="replace")
    assert "SMT solver failed" not in output, output
    assert proc.stderr == b"", proc.stderr
    statuses = summary(output)
    for prop, status in expected.items():
        assert statuses.get(prop) == status, output
