"""Boolean flags take a value, like the rest of the flags of their kind.

--smt_trace was a switch, with no value: `--smt_trace true` took `true` for
the input file. --arrays_rec false, which asks for nothing of the solver, was
rejected unless cvc5 was the solver selected.
"""

import re
import subprocess

import pytest

from conftest import common_args, kind2_bin, run_timeout

model = """
node main(x: int) returns (y: int);
let
  y = x;
  --%PROPERTY y = x;
tel
"""


def run(tmp_path, args):
    path = tmp_path / "model.lus"
    path.write_text(model)
    arg_list = [arg for pair in common_args.items() for arg in pair]
    proc = subprocess.run(
        [kind2_bin, *arg_list, *args, str(path)],
        capture_output=True,
        text=True,
        timeout=run_timeout,
    )
    return proc.returncode, re.sub(r"\x1b\[[0-9;]*m", "", proc.stdout + proc.stderr)


def traces(out_dir):
    return list(out_dir.rglob("*.smt2"))


@pytest.mark.parametrize("value", ["true", "on", "t"])
def test_smt_trace_enabled(tmp_path, value):
    out_dir = tmp_path / "out"
    code, out = run(tmp_path, ["--smt_trace", value, "--output_dir", str(out_dir)])
    assert code == 0, out
    assert traces(out_dir), out


@pytest.mark.parametrize("args", [[], ["--smt_trace", "false"], ["--smt_trace", "off"]])
def test_smt_trace_disabled(tmp_path, args):
    out_dir = tmp_path / "out"
    code, out = run(tmp_path, [*args, "--output_dir", str(out_dir)])
    assert code == 0, out
    assert not traces(out_dir), out


def test_smt_trace_requires_a_bool(tmp_path):
    # The input file is not taken for the value, or the value for the file
    code, out = run(tmp_path, ["--smt_trace"])
    assert code != 0, out
    assert "expected bool" in out, out


def test_smt_trace_usage_shows_value():
    proc = subprocess.run(
        [kind2_bin, "--help_of", "smt"],
        capture_output=True,
        text=True,
        timeout=run_timeout,
    )
    out = re.sub(r"\x1b\[[0-9;]*m", "", proc.stdout)
    assert "--smt_trace <bool>" in out, out


def test_arrays_rec_false_needs_no_solver(tmp_path):
    code, out = run(tmp_path, ["--arrays_rec", "false", "--only_parse", "true"])
    assert code == 0, out


def test_arrays_rec_true_needs_cvc5(tmp_path):
    code, out = run(
        tmp_path, ["--smt_solver", "z3", "--arrays_rec", "true", "--only_parse", "true"]
    )
    assert code != 0, out
    assert "--smt_solver cvc5" in out, out
