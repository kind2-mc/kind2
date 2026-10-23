"""A read of an enumerated value at an index variable past the size of an array.

A read of an enumerated value out of the bounds of an array is guarded so
that it denotes a value of the type (see #1727). A read at an index variable
whose range fits in the array is left unguarded, which takes the range of
each index variable from the bounds of its own dimension of the equation.

In the model, v[p][q] reads m[q][p]: the range [0, 2) of q fits the size 3
of m, and the range [0, 3) of p does not fit the size 2 of m[q]. Were the
ranges of p and q swapped, both would fit, and v[2][1], which reads m[1][2],
would be left unguarded. With --inline_arrays true, the elements of m are
constrained at the index 2 of m[q] anyway, so the property is checked with
--inline_arrays false too.
"""

import json
import subprocess

import pytest

from conftest import common_args, kind2_bin, run_timeout

model = """
type E = enum { A, B };
node main(m: E^2^3) returns ();
var v: bool^2^3;
let
  v = (((m[q][p] = A or m[q][p] = B) foreach q)^2 foreach p)^3;
  check "in_type" v[2][1];
tel
"""


@pytest.mark.parametrize("inline", ["true", "false"])
def test_array_read_oob_index_var(tmp_path, inline):
    path = tmp_path / "model.lus"
    path.write_text(model)
    args = common_args | {"--timeout": "20", "--inline_arrays": inline}
    arg_list = [arg for pair in args.items() for arg in pair]
    proc = subprocess.run(
        [kind2_bin, "-json", *arg_list, str(path)],
        capture_output=True,
        text=True,
        timeout=run_timeout,
    )
    objs = json.loads(proc.stdout)
    answers = {
        obj["name"]: obj["answer"]["value"]
        for obj in objs
        if obj.get("objectType") == "property"
    }
    assert answers == {"in_type": "valid"}, answers
