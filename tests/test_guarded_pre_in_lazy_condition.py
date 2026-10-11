"""A 'pre' guarded by '->' in a condition abstracted into a local of its own.

The guard of a lazy construct whose guarded operand is temporal, and the
condition of a restart, are abstracted into locals, outside of the '->' that
guards their 'pre'. The locals were defined at the initial state too, where
the 'pre' refers to offset -1, and the solver rejected the queries with an
unknown constant. The other engines prove the properties of the issue, so BMC
runs alone, on properties it can falsify: it reports each of them falsifiable
rather than failing (see #1744).
"""

import json
import subprocess

from conftest import common_args, kind2_bin, run_timeout

model = """
node Count() returns (n: int);
let
  n = 1 -> pre n + 1;
tel

node main(c: bool) returns ();
let
  check "==>" true -> (not pre c ==> Count() < 3);
  check "and then" true -> (pre c and then Count() >= 3);
  check "or else" true -> (pre c or else Count() < 3);
  check "when" true -> (when not pre c then Count() < 3 else true);
  check "restart" (0 -> (restart Count() every pre c)) < 3;
tel
"""

properties = ["==>", "and then", "or else", "when", "restart"]


def test_guarded_pre_in_lazy_condition(tmp_path):
    path = tmp_path / "model.lus"
    path.write_text(model)
    args = common_args | {"--timeout": "30", "--enable": "BMC"}
    arg_list = [arg for pair in args.items() for arg in pair]
    proc = subprocess.run(
        [kind2_bin, "-json", *arg_list, str(path)],
        capture_output=True,
        text=True,
        timeout=run_timeout,
    )
    objs = json.loads(proc.stdout)
    errors = [
        obj["value"]
        for obj in objs
        if obj.get("objectType") == "log" and obj.get("level") == "error"
    ]
    assert errors == [], errors
    answers = {
        obj["name"]: obj["answer"]["value"]
        for obj in objs
        if obj.get("objectType") == "property"
    }
    assert answers == {p: "falsifiable" for p in properties}, answers
