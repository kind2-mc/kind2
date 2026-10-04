"""The nodes generated for restarts.

A restart of an expression with state, such as a node call, is turned into a
call to a generated node, which a modular analysis reports as a system named
after its position. A restart only resets state, so 'restart e every r' is 'e'
when 'e' has no temporal operator and calls only functions, and the same for a
block of equations: no node is generated for it.

The outputs of a generated node have the base types of the values they stand
for, without the constraints of their refinement types: a constraint is
checked on the variable it is declared for, not again in the generated node.
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


refined = """
node N(x: int; r: bool) returns (y: subtype { n: int | n >= 0 });
let
  restart
    y = 0 -> pre y + (if x > 0 then x else 0);
  every r end
tel
"""


def test_refinement_type_checked_once(tmp_path):
    out = run_modular(tmp_path, refined)
    assert "SubType" in out, out
    subtypes = [l for l in out.splitlines() if "SubType" in l and ": valid" in l]
    assert subtypes and all(".restart_" not in l for l in subtypes), out
