"""A numeral followed by '..' is lexed as a numeral, not as a real literal.

The lexer reads a real literal with a trailing point, such as '2.' or
'0x1.' (issue #1896). By longest match, the slice '2..3' would then be lexed
as '2.' followed by '.3', and '0x1..0x2' as '0x1.' followed by '.', both
syntax errors. Kind 2 does not support array slices, so a slice that is lexed
correctly reaches the parser rule for slices, which reports it as an
unsupported operator.
"""

import pytest

from conftest import common_args, kind2_bin, run_kind2

model = """
node top(A: int^4) returns (B: int^2);
let
  --%MAIN;
  B = A[{}];
tel
"""


@pytest.mark.parametrize(
    "slice_", ["1..2", "1 .. 2", "0x1..0x2", "0x1 .. 0x2", "0..0x1", "0x0..1"]
)
def test_numeral_before_dotdot(tmp_path, slice_):
    lus = tmp_path / "slice.lus"
    lus.write_text(model.format(slice_))
    arg_list = [arg for pair in common_args.items() for arg in pair]
    proc = run_kind2([kind2_bin, *arg_list, "--only_parse", "true", str(lus)])
    output = proc.stdout.decode(errors="replace")
    assert "Unsupported operator: array slice" in output, output
    assert "Syntax Error" not in output, output
