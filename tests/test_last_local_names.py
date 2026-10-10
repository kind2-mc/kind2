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
var my_glast, other: int;
let
  frame (y)
    y = 0;
  let
    when m then
      y = last y + 1;
    end
  tel
  my_glast = y;
  other = y + 1;
  -- other is in the property, so that it is not sliced away
  check "p" my_glast < 1 or other < 0;
tel
"""


def table_names(output, header):
    """The names of the variables in the rows of a table of a counterexample,
    such as '== Locals ==', which ends at the first blank line"""
    lines = output.split(header, 1)[1].splitlines()[1:]
    names = []
    for line in lines:
        if not line.strip():
            break
        names.append(line.split()[0])
    return names


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
    # The table is there whatever is hidden, since 'other' is shown
    names = table_names(proc.stdout, "== Locals ==")
    assert "my_glast" in names
    # The local of 'last y', which is Kind 2 generated
    assert not any("glast_" in name for name in names)
