"""Kind 2 translates a node with thousands of stateless locals in a time
and a memory about linear in their number.

A node binds each of its stateless locals in a let of its own, around its
constraints, and a model generated from Simulink, a lookup table for
instance, has thousands of them. The lets were built one at a time, each
traversing and rebuilding the lets inside it, so a node of 2000 constant
locals took more than 3 GB before any engine started. They are now built as
one let per level of dependency, with one traversal of each term.

A binding moved to the wrong let would leave a local it refers to
unconstrained, and a property that holds would then have a counterexample:
the models below have properties that hold only if every local has the
value its equation gives it.
"""

import json

from conftest import common_args, kind2_bin, run_kind2


def answers(path, *extra, timeout=60):
    args = common_args | {"--timeout": str(timeout)}
    arg_list = [arg for pair in args.items() for arg in pair]
    proc = run_kind2(
        [kind2_bin, "-json", *arg_list, *extra, str(path)],
        timeout=timeout + 60,
    )
    try:
        objs = json.loads(proc.stdout)
    except json.JSONDecodeError:
        # A run that ran out of memory stops in the middle of its output
        raise AssertionError(proc.stderr.decode(errors="replace")[-2000:])
    return {
        obj["name"]: obj["answer"]["value"]
        for obj in objs
        if obj.get("objectType") == "property"
    }


# Locals on three levels of dependency, written out of order, and one of
# them, c, also taken at the previous instant, which the transition
# relation binds as well
levels = """
node main (x: int) returns (y: int);
var a, b, c, d: int;
let
  y = c + d;
  d = 0 -> pre c;
  c = b - a;
  b = a * 2;
  a = x + 1;
  check "holds" y = (x + 1) + (0 -> pre (x + 1));
  check "fails" y <> 3;
tel
"""

# Locals with the same dependencies in two nodes, one calling the other:
# the callee's lets end up in the caller's transition relation
call = """
node inc (x: int) returns (y: int);
var a, b: int;
let
  b = a + 1;
  a = x + 1;
  y = b;
tel

node main (x: int) returns (y: int);
var p, q: int;
let
  q = inc(p);
  p = x * 2;
  y = q;
  check "holds" y = 2 * x + 2;
  check "fails" y <> 4;
tel
"""


def test_let_levels_semantics(tmp_path):
    for name, model in {"levels": levels, "call": call}.items():
        path = tmp_path / f"{name}.lus"
        path.write_text(model)
        assert answers(path, "--enable", "BMC", "--enable", "IND") == {
            "holds": "valid",
            "fails": "falsifiable",
        }, name


def lookup_table(n):
    """A node like a lookup table generated from Simulink: n constant
    locals, and n locals each selecting one of them, so two levels"""
    consts = [f"  t{i} = {i};" for i in range(1, n + 1)]
    selects = [
        f"  s{i} = if x = {i} then t{i} else 0;" for i in range(1, n + 1)
    ]
    locals_ = ", ".join(
        [f"t{i}" for i in range(1, n + 1)] + [f"s{i}" for i in range(1, n + 1)]
    )
    total = " + ".join(f"s{i}" for i in range(1, n + 1))
    return f"""
node main (x: int) returns (y: int);
var {locals_}: int;
let
{chr(10).join(consts)}
{chr(10).join(selects)}
  y = {total};
  check "fails" y <> 7;
tel
"""


def test_many_stateless_locals(tmp_path):
    # 2000 stateless locals, which took more than 3 GB before any engine
    # started
    path = tmp_path / "table.lus"
    path.write_text(lookup_table(1000))
    assert answers(path, "--enable", "BMC") == {"fails": "falsifiable"}
