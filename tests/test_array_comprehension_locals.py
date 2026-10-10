"""The locals of array comprehensions are hidden from counterexamples.

An array comprehension is compiled to a fresh local named '<n>_gcomp', or to
a fresh ghost variable in a contract, which the counterexamples do not show.
A user variable whose name merely contains the segment 'gcomp', such as
'my_gcomp', is shown as any other.
"""

import subprocess

from conftest import common_args, kind2_bin, run_timeout

model = """
node N (A: int^3) returns (B: int^3);
var my_gcomp, other: int;
let
  B = (A[i] + 1 foreach i)^3;
  my_gcomp = B[0];
  other = B[1];
  -- other is in the property, so that it is not sliced away
  check "p" my_gcomp > A[1] or other < A[1];
tel
"""


contract_model = """
node N (A: int^3) returns (B: int^3);
(*@contract
  var my_gcomp: int = A[0];
  guarantee "g" B = (A[i] + my_gcomp foreach i)^3;
*)
let
  B = A;
tel
"""


def run(tmp_path, model):
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
    return proc.stdout


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
    output = run(tmp_path, model)
    # The table is there whatever is hidden, since 'other' is shown
    names = table_names(output, "== Locals ==")
    assert "my_gcomp" in names
    # The local of the comprehension, named 'gcomp_<n>' in the output
    assert not any(name.startswith("gcomp_") for name in names)


def test_counterexample_ghosts(tmp_path):
    output = run(tmp_path, contract_model)
    names = table_names(output, "== Ghosts ==")
    assert "my_gcomp" in names
    # The ghost variable of the comprehension in the guarantee
    assert not any("gcomp_" in name for name in names)
