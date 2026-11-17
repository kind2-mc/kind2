"""The interpreter reads a negative decimal between -1 and 0 as negative.

The sign of a decimal used to be taken from its integer part, which is zero
for '-0.375', so the input was read as 0.375 (issue #1894). '-.5' failed
altogether, the sign alone being read as the integer part.
"""

import json
import subprocess

import pytest

from conftest import common_args, kind2_bin, run_timeout

model = """
node top(r: real) returns (z: real);
let
  --%MAIN;
  z = r;
tel
"""

# Each input with the value it denotes, as a (numerator, denominator) pair
cases = [
    ("-0.375", (-3, 8)),
    ("-1.375", (-11, 8)),
    ("-3/8", (-3, 8)),
    ("-.5", (-1, 2)),
    ("-0.5e1", (-5, 1)),
    ("0.375", (3, 8)),
]


def interpret(tmp_path, input_file):
    lus = tmp_path / "sign.lus"
    lus.write_text(model)
    arg_list = [arg for pair in common_args.items() for arg in pair]
    proc = subprocess.run(
        [kind2_bin, "-json", *arg_list, "--enable", "interpreter",
         "--interpreter_input_file", str(input_file), str(lus)],
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
    [execution] = [obj for obj in objs if obj.get("objectType") == "execution"]
    [z] = [s for s in execution["trace"][0]["streams"] if s["name"] == "z"]
    return [(v["num"], v["den"]) for _, v in z["instantValues"]]


@pytest.mark.parametrize("fmt", ["csv", "json"])
def test_negative_decimal_input(tmp_path, fmt):
    if fmt == "csv":
        input_file = tmp_path / "input.csv"
        input_file.write_text("r," + ",".join(s for s, _ in cases) + "\n")
    else:
        input_file = tmp_path / "input.json"
        input_file.write_text(json.dumps([{"r": s} for s, _ in cases]))
    assert interpret(tmp_path, input_file) == [v for _, v in cases]
