"""A restart of an expression or a block without state needs no node.

A restart only resets state, so 'restart e every r' is 'e' when 'e' has no
temporal operator and calls only functions, and the same for a block of
equations. No node is generated for it, while a restart of an expression with
state, such as a node call, is still turned into a call to a generated node,
which a modular analysis reports as a system named after its position.
"""

import subprocess

from conftest import common_args, kind2_bin, run_timeout

stateless = """
function F (x: int) returns (y: int);
let y = 2 * x; tel

node top (a: int; r: bool) returns ();
var x1, x2, y1, y2: int;
let
  x1 = restart a + 1 every r;
  x2 = restart F(a) every r;
  restart
    y1 = a + 1;
    y2 = F(y1);
  every r end
  check "values" x1 = a + 1 and x2 = 2 * a and y2 = 2 * (a + 1);
tel
"""

stateful = """
node Cnt () returns (y: int);
let y = 0 -> pre y + 1; tel

node top (r: bool) returns ();
var x: int;
let
  x = restart Cnt() every r;
  check "reset" r => x = 0;
tel
"""


def run_modular(tmp_path, model):
    path = tmp_path / "model.lus"
    path.write_text(model)
    args = common_args | {"--timeout": "10", "--modular": "true"}
    arg_list = [arg for pair in args.items() for arg in pair]
    proc = subprocess.run(
        [kind2_bin, *arg_list, str(path)],
        capture_output=True,
        text=True,
        timeout=run_timeout,
    )
    return proc.stdout


def test_stateless_restart_generates_no_node(tmp_path):
    out = run_modular(tmp_path, stateless)
    assert "values: valid" in out, out
    assert ".restart_" not in out, out


def test_stateful_restart_generates_a_node(tmp_path):
    out = run_modular(tmp_path, stateful)
    assert "reset: valid" in out, out
    assert ".restart_" in out, out
