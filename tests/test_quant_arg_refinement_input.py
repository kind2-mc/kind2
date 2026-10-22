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

import subprocess

import pytest

from conftest import common_args, kind2_bin, run_timeout

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
        {"p": "valid"},
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
        {"p": "valid"},
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
        {"p": "valid"},
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
        {"p": "valid", "inc[L9C48].SubType[L2C15]": "valid"},
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
        {"p": "valid", "inc[L9C49].SubType[L2C15]": "invalid"},
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
        {"p": "valid", "inc[L10C26].SubType[L2C15]": "valid"},
    ),
}


def summary(output):
    """The status of each property in the summary of the run"""
    statuses = {}
    for section in output.split("Summary of Properties")[1:]:
        for line in section.splitlines():
            name, sep, rest = line.partition(": ")
            if sep and rest and not line.startswith(" "):
                statuses[name] = rest.split()[0]
    return statuses


@pytest.mark.parametrize("name", list(models))
def test_no_solver_error(tmp_path, name):
    model, expected = models[name]
    path = tmp_path / "model.lus"
    path.write_text(model)
    args = common_args | {"--timeout": "30"}
    arg_list = [arg for pair in args.items() for arg in pair]
    proc = subprocess.run(
        [kind2_bin, *arg_list, str(path)],
        capture_output=True,
        text=True,
        timeout=run_timeout,
    )
    assert "SMT solver failed" not in proc.stdout, proc.stdout
    statuses = summary(proc.stdout)
    for prop, status in expected.items():
        assert statuses.get(prop) == status, proc.stdout
