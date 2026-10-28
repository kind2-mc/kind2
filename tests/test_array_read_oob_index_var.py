"""A read of an enumerated value at an index variable past the size of an array.

A read of an enumerated value out of the bounds of an array is guarded so
that it denotes a value of the type (see #1727). A read at an index variable
whose range fits in the array is left unguarded, which takes the range of
each index variable from the bounds of its own dimension of the equation.

In the first model, v[p][q] reads m[q][p]: the range [0, 2) of q fits the
size 3 of m, and the range [0, 3) of p does not fit the size 2 of m[q]. Were
the ranges of p and q swapped, both would fit, and v[2][1], which reads
m[1][2], would be left unguarded.

In the second model, a[r] is read in the condition of an if-then-else under a
read at p, over every nesting order of p, q and r. The array a read at p is
compiled without the bound of p, which shifts the position of the bounds of
the index variables after it: the range of r is to be looked up among the
bounds of the equation, not of the array read at p. Otherwise, with r nested
in p and q in r, r would be given the range [0, 1) of q, which fits the size
2 of a.

With --inline_arrays true, the elements of an array are constrained at the
index equal to its size anyway, so the properties are checked with
--inline_arrays false too.
"""

import itertools
import json
import subprocess

import pytest

from conftest import common_args, kind2_bin, run_timeout

transposed = """
type E = enum { A, B };
node main(m: E^2^3) returns ();
var v: bool^2^3;
let
  v = (((m[q][p] = A or m[q][p] = B) foreach q)^2 foreach p)^3;
  check "in_type" v[2][1];
tel
"""


def nested(order):
    """The read of a[r] under a read at p, with the index variables nested in
    [order], the innermost first. The checked element has r = 2"""
    sizes = {"p": 2, "q": 1, "r": 3}
    expr = "(if (a[r] = A or a[r] = B) then t2 else f2)[p]"
    for v in order:
        expr = f"({expr} foreach {v})^{sizes[v]}"
    dims = "".join(f"^{sizes[v]}" for v in order)
    elem = "".join(f"[{2 if v == 'r' else 0}]" for v in reversed(order))
    return f"""
type E = enum {{ A, B }};
node main(a: E^2) returns ();
var w: bool{dims}; t2, f2: bool^2;
let
  t2 = true^2; f2 = false^2;
  w = {expr};
  check "in_type" w{elem};
tel
"""


models = [("transposed", transposed)] + [
    ("nested_" + "".join(order), nested(order))
    for order in itertools.permutations("pqr")
]


@pytest.mark.parametrize("inline", ["true", "false"])
@pytest.mark.parametrize("name, model", models, ids=[n for n, _ in models])
def test_array_read_oob_index_var(tmp_path, inline, name, model):
    path = tmp_path / f"{name}.lus"
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
