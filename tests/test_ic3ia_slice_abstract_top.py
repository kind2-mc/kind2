"""IC3IA on a property of an abstract top node, sliced to the property.

IC3IA slices the system to each property. An imported node with modes is
analyzed on its own to check its modes, abstracted by its contract, and the
slicing of an abstract node used to keep only the roots of the assumptions
of its contract, not the state variables of the property. The ghost variable
of the contract was sliced away, its subtype check was unconstrained, and
IC3IA falsified it although the guarantee makes it hold (#1881).
"""

import subprocess

import pytest

from conftest import common_args, kind2_bin, run_timeout

model = """
type Pos = subtype { x: int | x >= 1 };

function imported F(y: int) returns (x: int);
(*@contract
  guarantee x >= {bound};
  var l: Pos = x;
  mode m (require y > 0;);
  mode n (require y <= 0;);
*)
"""


def run_ic3ia(tmp_path, bound, slicing):
    path = tmp_path / "model.lus"
    path.write_text(model.replace("{bound}", str(bound)))
    args = common_args | {"--timeout": "30", "--slice_nodes": slicing}
    arg_list = [arg for pair in args.items() for arg in pair]
    run = subprocess.run(
        [kind2_bin, *arg_list, "--enable", "IC3IA", str(path)],
        capture_output=True,
        text=True,
        timeout=run_timeout,
    )
    output = run.stdout + run.stderr
    assert "Runtime failure" not in output, output
    assert "terminated on exception" not in output, output
    return output


@pytest.mark.parametrize("slicing", ["on", "off"])
def test_ghost_subtype_proved(tmp_path, slicing):
    output = run_ic3ia(tmp_path, 1, slicing)
    assert "Generated property SubType[L7C7] is valid by property " \
        "directed reachability (IA)" in output, output


# A guarantee too weak for the subtype: the check is still falsified
@pytest.mark.parametrize("slicing", ["on", "off"])
def test_ghost_subtype_falsified(tmp_path, slicing):
    output = run_ic3ia(tmp_path, 0, slicing)
    assert "Property SubType[L7C7] is invalid by property " \
        "directed reachability (IA)" in output, output
