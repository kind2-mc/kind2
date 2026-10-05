"""The program written by `--minimize_program valid_lustre` is valid Lustre.

The minimized program replaces the expressions outside the IVC with calls
to a fresh imported node `__rand<n>`. That node was declared `opaque`, an
annotation the front end rejects on a node without a contract, so feeding
the minimized program back to Kind 2 failed with a parse error.

The model is not in the regression tree, which does not run IVC.
"""

import subprocess

from conftest import common_args, kind2_bin, run_timeout

model = """
node arm (x: int) returns (y: int);
let
  y = x;
tel

node main () returns (ok: bool; z: int);
let
  ok = arm(5) = 5;
  z = arm(3);
  check ok;
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


def test_minimized_valid_lustre_program_parses(tmp_path):
    path = tmp_path / "ivc_minimized_program.lus"
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
        assert "__rand" in program.read_text(), program.read_text()
        rerun = run_kind2(
            common_args | {"--output_dir": str(tmp_path / "out")}, program
        )
        assert "Parser error" not in rerun.stdout, rerun.stdout
        assert "Summary of Properties" in rerun.stdout, rerun.stdout
