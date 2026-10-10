"""The locals of array comprehensions are hidden from counterexamples.

An array comprehension is compiled to a fresh local named '<n>_gcomp', which
the counterexamples do not show. A user variable whose name merely contains
the segment 'gcomp', such as 'my_gcomp', is shown as any other.
"""

import subprocess

from conftest import common_args, kind2_bin, run_timeout

model = """
node N (A: int^3) returns (B: int^3);
var my_gcomp: int;
let
  B = (A[i] + 1 foreach i)^3;
  my_gcomp = B[0];
  check "p" my_gcomp > A[1];
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
    locals_section = proc.stdout.split("== Locals ==", 1)[1]
    assert "my_gcomp" in locals_section
    # The local of the comprehension, named 'gcomp_<n>' in the output
    assert "gcomp_" not in locals_section
