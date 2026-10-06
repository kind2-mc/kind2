"""A function that copies an array whole has a definition at the SMT level.

The definitions of the recursive functions, and of the functions they call,
are built from the equations of their bodies (see LustreFunDefs). An array
equation y = x is compiled to an equation for every index, y[i] = x[i], which
no definition was built from, and no function with an output or local
variable of an array type was defined. A function whose body called such a
function was not defined either. A copy of a whole array is now defined as
the array it copies, and an array-typed local variable defined by a call no
longer stands in the way.

Without the theory of arrays (--smt_arrays false), the selects of a
definition are encoded as applications of select symbols. They were encoded
once the bindings of the body were nested in let terms, where a select of an
array-typed local variable applies to a bound variable, which the encoding
failed on with Invalid_argument("indexes_of_select"). The selects of each
binding are now encoded before the bindings are nested.
"""

import json
import re
import subprocess

import pytest

from conftest import common_args, kind2_bin, run_timeout

model = """
type BigA = subtype { v: int^1 | v[0] >= 100 };

function Asc(x: BigA) returns (y: int^1);
let
  y = x;
tel

function G(a: int^1) returns (y: int);
let
  y = Asc(a)[0];
tel

function rec F(a: int^1; n: int) returns (y: int);
con
  decreases n;
noc
let
  y = when n <= 0 then 0 else F(a, n - 1) + 0 * G(a);
tel

node N(x: int; a: int^1) returns (y: bool);
let
  y = F(a, x) = x;
  check y;
tel
"""


@pytest.mark.parametrize("arrays", ["false", "true"])
def test_whole_array_copy_is_defined(tmp_path, arrays):
    path = tmp_path / "rec_def_whole_array_copy.lus"
    path.write_text(model)
    args = common_args | {"--timeout": "60", "--smt_arrays": arrays}
    arg_list = [arg for pair in args.items() for arg in pair]
    proc = subprocess.run(
        [
            kind2_bin,
            "-json",
            *arg_list,
            "--smt_trace",
            "--output_dir",
            str(tmp_path / "out"),
            str(path),
        ],
        capture_output=True,
        text=True,
        timeout=run_timeout,
    )
    errors = [
        obj["value"]
        for obj in json.loads(proc.stdout)
        if obj.get("objectType") == "log"
        and obj.get("level") in ("error", "fatal")
    ]
    assert errors == [], errors
    traces = "".join(
        trace.read_text() for trace in (tmp_path / "out").rglob("*.smt2")
    )
    for function in ["Asc", "G"]:
        assert re.search(
            r"\(define-fun\s+" + function + r"\.y\.__function_definition\s",
            traces,
        ), function
