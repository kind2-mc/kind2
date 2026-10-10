"""The locals that desugar the 'last' operator are told apart by their name.

They are named '<n>_glast_<x>', and hidden from counterexamples. A user
variable whose name merely has the segment 'glast', such as 'my_glast', is
shown as any other (its refinement type is checked too, see
regression/falsifiable/user_var_named_like_last_local.lus).
"""

import subprocess

from conftest import common_args, kind2_bin, run_timeout

model = """
node N (m: bool) returns (y: int);
var my_glast: int;
let
  frame (y)
    y = 0;
  let
    when m then
      y = last y + 1;
    end
  tel
  my_glast = y;
  check "p" my_glast < 1;
tel
"""


def test_counterexample_locals(tmp_path):
    path = tmp_path / "model.lus"
    path.write_text(model)
    args = common_args | {"--timeout": "30"}
    arg_list = [arg for pair in args.items() for arg in pair]
    proc = subprocess.run(
        [kind2_bin, *arg_list, str(path)],
        capture_output=True,
        text=True,
        timeout=run_timeout,
    )
    assert "invalid after" in proc.stdout
    locals_section = proc.stdout.split("== Locals ==", 1)[1].split("\n\n", 1)[0]
    assert "my_glast" in locals_section
    # The local of 'last y', which is Kind 2 generated
    assert "glast_y" not in locals_section and "glast_" not in locals_section.replace("my_glast", "")
