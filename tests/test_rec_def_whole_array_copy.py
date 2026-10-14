"""A function that copies an array whole has a definition at the SMT level.

The definitions of the recursive functions, and of the functions they call,
are built from the equations of their bodies (see LustreFunDefs). An array
equation y = x is compiled to an equation for every index, y[i] = x[i], which
no definition was built from, and no function with an output or local
variable of an array type was defined. A function whose body called such a
function was not defined either. A copy of a whole array is now defined as
the array it copies, and an array-typed local variable defined by a call no
longer stands in the way. Any other equation for every index, such as
the one an array comprehension is compiled to, still leaves the function
without a definition.

Without the theory of arrays (--smt_arrays false), the selects of a
definition are encoded as applications of select symbols. They were encoded
once the bindings of the body were nested in let terms, where a select of an
array-typed local variable applies to a bound variable, which the encoding
failed on with Invalid_argument("indexes_of_select"). The selects of each
binding are now encoded before the bindings are nested.

The definitions of the functions a recursive function calls are given to the
supervisor when it checks a counterexample that reaches a recursive call
past the unrollings. In the model, the subtype obligation of Asc in the
recursive call of F is such a counterexample.
"""

import json
import re
import subprocess

import pytest

from conftest import common_args, kind2_bin, run_timeout


def model(ty, body, select):
    return f"""
type BigA = subtype {{ v: {ty} | v{select} >= 100 }};

function Asc(x: BigA) returns (y: {ty});
let
  {body};
tel

function G(a: {ty}) returns (z: int);
let
  z = Asc(a){select};
tel

function rec F(a: {ty}; n: int) returns (r: int);
con
  decreases n;
noc
let
  r = when n <= 0 then 0 else F(a, n - 1) + 0 * G(a);
tel

node N(x: int; a: {ty}) returns ();
let
  -- Falsified at x = 1, within the unrollings. Any x >= 1 falsifies
  -- F(a, x) = x, but a counterexample with a larger x reaches a call of F
  -- past the unrollings, which is not evaluated with an array argument, and
  -- would leave the property unknown
  check "p" x = 1 => F(a, x) = x;
tel
"""


def run(tmp_path, lustre, arrays):
    path = tmp_path / "rec_def_whole_array_copy.lus"
    path.write_text(lustre)
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
    objs = json.loads(proc.stdout)
    logs = [obj for obj in objs if obj.get("objectType") == "log"]
    errors = [
        log["value"] for log in logs if log.get("level") in ("error", "fatal")
    ]
    assert errors == [], errors
    # The supervisor checked a counterexample past the unrollings, so the
    # definitions the functions have were given to it
    assert any(
        "Counterexamples reach a recursive call of F" in log["value"]
        for log in logs
    ), logs
    answers = {
        obj["name"]: obj["answer"]["value"]
        for obj in objs
        if obj.get("objectType") == "property"
    }
    assert answers.get("p") == "falsifiable", answers
    traces = "".join(
        trace.read_text() for trace in (tmp_path / "out").rglob("*.smt2")
    )
    return " ".join(traces.split())


def definition(traces, name):
    """The define-fun command of [name], if any"""
    start = traces.find("(define-fun " + name + " ")
    if start < 0:
        return None
    depth = 0
    for end in range(start, len(traces)):
        if traces[end] == "(":
            depth += 1
        elif traces[end] == ")":
            depth -= 1
            if depth == 0:
                return traces[start : end + 1]
    return None


@pytest.mark.parametrize("arrays", ["false", "true"])
@pytest.mark.parametrize(
    "ty, select", [("int^2", "[1]"), ("int^2^2", "[0][1]")]
)
def test_whole_array_copy_is_defined(tmp_path, arrays, ty, select):
    traces = run(tmp_path, model(ty, "y = x", select), arrays)
    asc = definition(traces, "Asc.y.__function_definition")
    assert asc, "no definition of Asc"
    # The output of Asc is its input, its only formal parameter
    formal = re.match(r"\(define-fun \S+ \(\((\S+) ", asc).group(1)
    assert re.search(
        r" \(let \(\((\S+) " + re.escape(formal) + r"\)\) \1\)\)$", asc
    ), asc
    assert definition(traces, "G.z.__function_definition"), "no definition of G"


@pytest.mark.parametrize("arrays", ["false", "true"])
@pytest.mark.parametrize(
    "ty, body, select",
    [
        ("int^2^2", "y = (x[j][i] foreach i, j)^2^2", "[0][1]"),
        ("int^2", "y = (x[0] foreach i)^2", "[1]"),
        ("int^2", "y = (x[1 - i] foreach i)^2", "[1]"),
        ("int^2", "y = (x[i] + 1 foreach i)^2", "[1]"),
    ],
)
def test_other_array_equation_is_not_defined(tmp_path, arrays, ty, body, select):
    traces = run(tmp_path, model(ty, body, select), arrays)
    assert not definition(traces, "Asc.y.__function_definition")
    assert not definition(traces, "G.z.__function_definition")
