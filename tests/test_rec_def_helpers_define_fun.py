"""The definition of a function a recursive definition applies is not recursive.

A recursive function applied to quantified variables is defined at the SMT
level, and so is every function its definition calls that is neither
recursive nor imported (see LustreFunDefs). Each such definition was given
to the solver in a define-funs-rec command of its own. A solver unfolds a
function of define-funs-rec on demand rather than expanding it as a macro, so
every unfolding of the recursive function needed further unfoldings of its
helpers, and a model whose recursive function calls a few helpers went from
seconds to not finishing. A definition that applies no symbol of its own
block is now given with define-fun.
"""

import re
import subprocess

from conftest import common_args, kind2_bin, run_timeout

model = """
function H (x: int) returns (y: bool);
let
  y = x >= 0;
tel

function rec AllNonNeg (n: int) returns (r: bool);
con
  decreases n;
noc
let
  r = when n <= 0 then H(n + 1) else H(n) and AllNonNeg(n - 1);
tel

node main () returns ();
let
  check "q" forall (n: int) n >= 0 => (AllNonNeg(n) or not AllNonNeg(n));
tel
"""


def commands(text, name):
    """The s-expressions of the commands [name] in an SMT trace"""
    found = []
    for match in re.finditer(r"\(" + re.escape(name) + r"\s", text):
        depth = 0
        for end in range(match.start(), len(text)):
            if text[end] == "(":
                depth += 1
            elif text[end] == ")":
                depth -= 1
                if depth == 0:
                    found.append(text[match.start() : end + 1])
                    break
    return found


def test_helper_definitions_are_not_recursive(tmp_path):
    path = tmp_path / "rec_def_helper.lus"
    path.write_text(model)
    arg_list = [arg for pair in common_args.items() for arg in pair]
    proc = subprocess.run(
        [
            kind2_bin,
            *arg_list,
            "--smt_trace",
            "--output_dir",
            str(tmp_path / "out"),
            str(path),
        ],
        capture_output=True,
        text=True,
        timeout=run_timeout,
    )
    assert proc.returncode == 0, proc.stdout
    traces = "".join(
        trace.read_text() for trace in (tmp_path / "out").rglob("*.smt2")
    )
    rec_blocks = commands(traces, "define-funs-rec")
    assert any("AllNonNeg" in block for block in rec_blocks), rec_blocks
    assert not any("H.y.__function_definition (" in block for block in rec_blocks)
    assert re.search(r"\(define-fun\s+H\.y\.__function_definition\s", traces)
