"""IC3QE on an activated call that takes an array as input.

The temporal branch of the 'when' expression is abstracted into a call that
the guard activates. The call takes the array A as input and passes it
through a shadow variable, so its transition relation equates two arrays.
QE generalization evaluated that equation in a model and failed an assertion
in Simplify.relation, which only takes integers, reals and bitvectors.

The solver does not eliminate the array variables of the generalization, so
IC3QE still shuts down without a result here, but as an unsupported feature,
and not on an exception. The test checks for that message, so that it fails
if IC3QE stops before it generalizes, and the equation is never evaluated. It
has to be updated once the solver eliminates the array variables.
"""

import subprocess

from conftest import common_args, kind2_bin, run_timeout

model = """
node main(s: int) returns (A: int^3; y: int);
let
  A = [s, s, s];
  y = when s > 0 then (-1 -> pre A[1]) else 0;
  check y = 0 or y = -1 or y > 0;
tel
"""


def test_ic3qe_array_equation(tmp_path):
    path = tmp_path / "ic3qe_array_equation.lus"
    path.write_text(model)
    args = common_args | {"--timeout": "20"}
    arg_list = [arg for pair in args.items() for arg in pair]
    run = subprocess.run(
        [kind2_bin, *arg_list, "--enable", "IC3QE", str(path)],
        capture_output=True,
        text=True,
        timeout=run_timeout,
    )
    output = run.stdout + run.stderr
    assert "terminated on exception" not in output, output
    assert "Runtime error" not in output, output
    assert "Assertion failed" not in output, output
    assert "Shutting down IC3QE: QE failed during generalization step" in output, output
