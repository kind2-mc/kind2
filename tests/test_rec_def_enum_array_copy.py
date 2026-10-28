"""An element-wise copy of an array of enumerated values has a definition.

A read of an enumerated value out of the bounds of an array is guarded so
that it denotes a value of the type (see #1727). A read at an index variable
whose range fits in the array is never out of the bounds, and is left
unguarded: the equation of an element-wise copy, y = (x[i] foreach i)^2, is
still a whole-array copy that a definition is built from (see
test_rec_def_whole_array_copy.py).
"""

import pytest

from test_rec_def_whole_array_copy import definition, run


def model(ty, body):
    return f"""
type E = enum {{ A, B }};
type BigA = subtype {{ v: {ty} | v[1] = B }};

function Asc(x: BigA) returns (y: {ty});
let
  {body};
tel

function G(a: {ty}) returns (z: E);
let
  z = Asc(a)[1];
tel

function rec F(a: {ty}; n: int) returns (r: int);
con
  decreases n;
noc
let
  r = when n <= 0 then 0 else F(a, n - 1) + 0 * (if G(a) = A then 1 else 0);
tel

node N(x: int; a: {ty}) returns ();
let
  check "p" x = 1 => F(a, x) = x;
tel
"""


@pytest.mark.parametrize("arrays", ["false", "true"])
@pytest.mark.parametrize(
    "body", ["y = x", "y = (x[i] foreach i)^2"]
)
def test_enum_array_copy_is_defined(tmp_path, arrays, body):
    traces = run(tmp_path, model("E^2", body), arrays)
    assert definition(traces, "Asc.y.__function_definition"), "no definition of Asc"
    assert definition(traces, "G.z.__function_definition"), "no definition of G"
