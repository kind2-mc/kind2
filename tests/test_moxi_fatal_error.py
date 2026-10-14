"""kmoxi reports every fatal error as an SMT-LIB error.

A model kmoxi cannot parse, an input file it cannot open, and an error on
the command line are each reported on the standard output as a single
(error "...") line, with the exit code they had before: kmoxi used to print
the first two on the standard error, and the usage text, with color codes,
for the last.
"""

import pytest

from conftest import run_kmoxi_process

ERROR = 1
USAGE_ERROR = 2
PARSE_ERROR = 3

model = """(set-logic QF_LIA)
(define-system main :input ((i Int))
(
"""


@pytest.fixture
def path(tmp_path):
    path = tmp_path / "model.moxi"
    path.write_text(model)
    return path


def check_error(res, code, message):
    assert res.returncode == code, res.stdout + res.stderr
    assert res.stdout == f'(error "{message}")\n', res.stdout
    assert res.stderr == "", res.stderr


@pytest.mark.parametrize("extra", [(), ("--only_parse", "true")])
def test_syntax_error(path, extra):
    res = run_kmoxi_process(path, *extra)
    check_error(res, PARSE_ERROR, f"{path}:3:1: syntax error")


def test_missing_file(tmp_path):
    missing = tmp_path / "missing.moxi"
    res = run_kmoxi_process(missing)
    check_error(
        res, ERROR,
        f"Error opening input file: {missing}: No such file or directory",
    )


@pytest.mark.parametrize("color", ["false", "true"])
def test_unknown_flag(path, color):
    res = run_kmoxi_process(path, "--color", color, "--bogus_flag")
    check_error(res, USAGE_ERROR, "unknown flag --bogus_flag")


def test_bad_flag_value(path):
    # The quotes of the message are doubled, as in an SMT-LIB string
    res = run_kmoxi_process(path, "--color", "maybe")
    check_error(
        res, USAGE_ERROR,
        'error on flag --color: expected bool but got ""maybe""',
    )


def test_two_input_files(path):
    res = run_kmoxi_process(path, path)
    check_error(res, USAGE_ERROR, f"More than one input file given: {path}")
