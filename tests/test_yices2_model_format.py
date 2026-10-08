"""Yices 2.6.2 up to 2.6.x print SMT-LIB models only when given
--smt2-model-format. Yices 2.7.0 prints them by default and no longer has
that option: it exits on it at once, so Kind 2 passed it to every version
newer than 2.6.1, and every query to Yices 2.7.0 failed.

A wrapper reports a given version, records the arguments it is started with,
and lets the real Yices answer everything else. It drops
--smt2-model-format, so that the real Yices accepts the run whatever its
version. The property is proved, so no model is read in the wrapped runs.

The unwrapped runs use the installed Yices as it is: one falsifies a
property, which reads a model, and the other proves one.
"""

import shutil
import subprocess
import sys

import pytest

from conftest import common_args, kind2_bin, run_timeout

valid_model = """
node main (x: int) returns (y: int);
let
  y = if x > 0 then x else -x;
  check y >= 0;
tel
"""

invalid_model = """
node main (x: int) returns (y: int);
let
  y = x;
  check y <> 4;
tel
"""

yices = shutil.which("yices-smt2")

needs_yices = pytest.mark.skipif(
    yices is None, reason="needs yices-smt2"
)


def run_kind2(path, flags):
    args = common_args | {"--timeout": "20"}
    arg_list = [arg for pair in args.items() for arg in pair]
    return subprocess.run(
        [kind2_bin, *arg_list, "--smt_solver", "Yices2", *flags, str(path)],
        capture_output=True,
        text=True,
        timeout=run_timeout,
    )


@needs_yices
@pytest.mark.skipif(
    sys.platform == "win32",
    reason="needs a POSIX shell to stand in for another version",
)
@pytest.mark.parametrize(
    "version, model_option",
    [
        ("2.6.1", False),
        ("2.6.2", True),
        ("2.6.5", True),
        ("2.7.0", False),
        ("2.7.1", False),
        ("3.0.0", False),
    ],
)
def test_yices2_model_option(tmp_path, version, model_option):
    path = tmp_path / "model.lus"
    path.write_text(valid_model)
    log = tmp_path / "args.log"
    wrapper = tmp_path / "yices-smt2"
    wrapper.write_text(
        "#!/bin/sh\n"
        f'if [ "$1" = "--version" ]; then echo "Yices {version}"; exit 0; fi\n'
        f'echo "$@" >> "{log}"\n'
        'for arg; do\n'
        '  shift\n'
        '  if [ "$arg" != "--smt2-model-format" ]; then set -- "$@" "$arg"; fi\n'
        'done\n'
        f'exec "{yices}" "$@"\n'
    )
    wrapper.chmod(0o755)
    run = run_kind2(path, ["--yices2_bin", str(wrapper)])
    assert run.returncode == 0, run.stdout + run.stderr
    starts = log.read_text().splitlines()
    assert starts, run.stdout
    for start in starts:
        assert ("--smt2-model-format" in start.split()) == model_option, start


@needs_yices
@pytest.mark.parametrize(
    "model, code",
    [(valid_model, 0), (invalid_model, 40)],
    ids=["valid", "falsified"],
)
def test_installed_yices2(tmp_path, model, code):
    path = tmp_path / "model.lus"
    path.write_text(model)
    run = run_kind2(path, [])
    assert run.returncode == code, run.stdout + run.stderr
    assert "<Error>" not in run.stdout, run.stdout
