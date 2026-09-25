"""Test generation runs on a node whose modes have no ensures.

Test generation explores which combinations of the modes of a node can be
active, and the activation of a mode only depends on its requires. A node
whose modes have no ensures has no effective contract, as nothing in it
constrains its outputs, and test generation was skipped on it: the node
it runs on was required to have an effective contract, not modes.

The model is not in the regression tree, which does not run test generation.
"""

import subprocess

from conftest import common_args, kind2_bin, run_timeout

model = """
node main (x: int) returns (y: int);
(*@contract
  mode pos (require x > 0;);
  mode nonpos (require x <= 0;);
*)
let
  y = x + 1;
tel
"""


def test_testgen_on_modes_without_ensures(tmp_path):
    path = tmp_path / "testgen_modes_without_ensures.lus"
    path.write_text(model)
    out_dir = tmp_path / "out"
    args = common_args | {"--testgen": "true", "--output_dir": str(out_dir)}
    arg_list = [arg for pair in args.items() for arg in pair]
    run = subprocess.run(
        [kind2_bin, *arg_list, str(path)],
        capture_output=True,
        text=True,
        timeout=run_timeout,
    )
    assert "skipping test generation" not in run.stdout, run.stdout
    assert (out_dir / "main" / "tests" / "unit.xml").is_file(), run.stdout
