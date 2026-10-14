"""kmoxi reports every fatal error as an SMT-LIB error.

A model kmoxi cannot parse, an input file it cannot open, and an error on
the command line are each reported on the standard output as a single
(error "...") line, with the exit code they had before: kmoxi used to print
the first two on the standard error, and the usage text, with color codes,
for the last.
"""

import subprocess

import pytest

from conftest import kind2_bin, kmoxi_bin, run_kind2, run_kmoxi_process

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


def test_syntax_error_no_arguments():
    # Without any argument, kmoxi reads the model from the standard input
    if not kmoxi_bin.exists():
        pytest.skip(f"{kmoxi_bin} is not built (make kmoxi)")
    res = subprocess.run(
        [kmoxi_bin], input=model, capture_output=True, text=True, timeout=30
    )
    check_error(res, PARSE_ERROR, "(stdin):3:1: syntax error")


def test_missing_file(tmp_path):
    missing = tmp_path / "missing.moxi"
    res = run_kmoxi_process(missing)
    check_error(
        res, ERROR,
        f"Error reading input file {missing}: No such file or directory",
    )


def test_directory(tmp_path):
    # The message of the system does not name the file: the error does
    res = run_kmoxi_process(tmp_path)
    check_error(res, ERROR, f"Error reading input file {tmp_path}: Is a directory")


def test_empty_argument():
    # An empty file name is not the standard input
    res = run_kmoxi_process("")
    check_error(res, USAGE_ERROR, "Empty input file name")
    # kind2 reports it as a usage error too, rather than crashing on it
    if not kind2_bin.exists():
        pytest.skip(f"{kind2_bin} is not built")
    res = run_kind2([kind2_bin, ""])
    assert res.returncode == USAGE_ERROR, res.stdout + res.stderr
    assert b"Empty input file name" in res.stdout + res.stderr, res.stdout


def test_invalid_utf_8(tmp_path):
    # The lexer reports the unexpected byte 0xe9, not valid UTF-8 alone: it
    # is replaced, and the line is valid UTF-8
    path = tmp_path / "latin1.moxi"
    path.write_bytes(b"(set-logic QF_LIA)\n\xe9\n")
    res = run_kmoxi_process(path)
    assert "\ufffd" not in res.stdout, res.stdout
    check_error(res, PARSE_ERROR,
                f"{path}:2:1: error: unexpected character \u2018?\u2019")


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
