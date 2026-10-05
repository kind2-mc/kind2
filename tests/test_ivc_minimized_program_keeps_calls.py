"""The program written by `--minimize_program` keeps the arguments of the
node calls in the IVC.

The arguments of a node call are not model elements of their own. The
minimized program replaced every argument that is not an identifier with an
undefined value, even when the call itself was in the IVC, so the property
could be invalid in the minimized program.

The model is not in the regression tree, which does not run IVC.
"""

import subprocess

from conftest import common_args, kind2_bin, run_timeout

model = """
node arm (x: int) returns (y: int);
let
  y = x;
tel

node main (z: int) returns (ok1, ok2: bool);
let
  ok1 = arm(5) = 5;
  ok2 = z + 1 = arm(z + 1);
  check ok1;
  check ok2;
tel
"""


def run_kind2(args, path):
    arg_list = [arg for pair in args.items() for arg in pair]
    return subprocess.run(
        [kind2_bin, *arg_list, str(path)],
        capture_output=True,
        text=True,
        timeout=run_timeout,
    )


def test_minimized_program_keeps_call_arguments(tmp_path):
    path = tmp_path / "ivc_minimized_calls.lus"
    path.write_text(model)
    min_dir = tmp_path / "minimized"
    run = run_kind2(
        common_args
        | {
            "--ivc": "true",
            "--minimize_program": "valid_lustre",
            "--ivc_output_dir": str(min_dir),
            "--output_dir": str(tmp_path / "out"),
        },
        path,
    )
    minimized = sorted(min_dir.glob("*.lus"))
    assert minimized, run.stdout
    for program in minimized:
        rerun = run_kind2(
            common_args | {"--output_dir": str(tmp_path / "out")}, program
        )
        assert "is valid" in rerun.stdout, rerun.stdout
        assert "is invalid" not in rerun.stdout, rerun.stdout
