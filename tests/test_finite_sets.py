"""Sets and maps are finite: no counterexample relying on an infinite one is
reported.

Sets are encoded as arrays, which may be infinite. Only a quantifier over
their elements, or a function called within one, can tell, unless the
counterexample satisfies it with a witness (a forall in an invariant
property, an exists in a reachable one). For the set types such a quantifier
observes, a counterexample to a property depending on such a set is checked
on the system with the finiteness constraints, and reported if one with the
same inputs is found there; otherwise the analysis runs again on that system,
and the counterexample is only reported if it is found again (see
FiniteSets). The other models, and the properties that depend on no such
set, are analyzed as before.

Possibly infinite sets and maps (iset, imap) have no finiteness constraints:
a counterexample relying on an infinite one is genuine.
"""

import json
import subprocess

import pytest

from conftest import common_args, kind2_bin, run_timeout

RESTART_LOG = "applying the finiteness constraints"

models = {
    # Every finite set of integers misses one: only an infinite set
    # falsifies the property
    "spurious": """
node main (s: set<int>) returns ();
let
  check "outside" exists (i: int) not (i in s);
tel
""",
    # The counterexamples are genuine. The forall of "nonneg" is falsified,
    # by one element: its counterexample needs no finiteness constraint
    "genuine": """
node main (s: set<int>) returns ();
let
  check "nonneg" forall (i: int) (i in s) => i >= 0;
  check "no_one" not (1 in s);
tel
""",
    # No quantifier: the sets are left as they are
    "quantifier_free": """
node main (s: set<int>; x: int) returns ();
let
  check "member" x in s + { x };
  check "no_one" not (1 in s);
tel
""",
    # A quantifier observes the set, but the property falsified does not
    # depend on it
    "unrelated": """
node main (s: set<int>; x: int) returns ();
let
  check "pos" x > 0;
  check "trivial" forall (i: int) (i in s) => (i in s);
tel
""",
    # A set of Booleans is finite whatever its encoding
    "finite_elements": """
node main (s: set<bool>) returns ();
let
  check "outside" exists (b: bool) not (b in s);
tel
""",
    # The exists may observe an infinite set, but the counterexample, the
    # empty set, is one of the system with the finiteness constraints: its
    # check confirms it, and the analysis does not run again
    "confirmed": """
node main (s: set<int>) returns ();
let
  check "nonempty" exists (i: int) i in s;
tel
""",
    # An exists in a reachable property is satisfied by one element: the
    # witness needs no finiteness constraint
    "reachable_exists": """
node main (s: set<int>) returns ();
let
  check reachable "witness" exists (i: int) (i in s) and i > 5;
tel
""",
    # Only an infinite set reaches the forall
    "reachable_forall": """
node main (s: set<int>) returns ();
let
  check reachable "everything" forall (i: int) i in s;
tel
""",
    # The set, a free constant, is only observed by a function called within
    # the quantifier: its finiteness constraints are applied lazily too
    # A possibly infinite set: the infinite set is a genuine counterexample
    "iset": """
node main (s: iset<int>) returns ();
let
  check "outside" exists (i: int) not (i in s);
tel
""",
    # The same for the keys of a possibly infinite map
    "imap": """
node main (m: imap<int, bool>) returns ();
let
  check "outside" exists (i: int) not (i in m);
tel
""",
    # A finite set is a possibly infinite one: literals, finite sets and
    # calls with finite arguments define possibly infinite sets
    "iset_from_set": """
node f (a: iset<int>) returns (b: iset<int>);
let
  b = a + { 0 };
tel

node main (x: int; t: set<int>) returns (s, u: iset<int>);
let
  s = { x } -> {}@<int> + pre s + { x };
  u = f(t);
  check "member" x in s;
  check "same" s = t => (x in t);
tel
""",
    # A use of a set of finite elements does not hide another use of a set
    # of the same base type, whose elements are not finite
    "refined_first": """
type nat10 = subtype { x: int | 0 <= x and x <= 10 };
node main (b: set<nat10>; s: set<int>) returns ();
let
  check "p" exists (i: int) (i in b) or not (i in s);
tel
""",
    # An intersection is finite when one operand is, and a difference when
    # its left operand is
    "finite_set_ops": """
node main (s: set<int>; u: iset<int>) returns (t1, t2: set<int>);
let
  t1 = s * u;
  t2 = s - u;
  check "inter" (0 in t1) => (0 in s);
  check "diff" (0 in t2) => not (0 in u);
tel
""",
    "via_function": """
const S: set<int>;

function f (i: int) returns (b: bool);
let
  b = i in S;
tel

node main () returns ();
let
  check "outside" exists (i: int) not f(i);
tel
""",
}

# The answers expected, and whether the analysis runs again with the
# finiteness constraints
expected = {
    "spurious": ({"outside": "unknown"}, True),
    "genuine": ({"nonneg": "falsifiable", "no_one": "falsifiable"}, False),
    "confirmed": ({"nonempty": "falsifiable"}, False),
    "reachable_exists": ({"witness": "reachable"}, False),
    "reachable_forall": ({"everything": "unknown"}, True),
    "quantifier_free": ({"member": "valid", "no_one": "falsifiable"}, False),
    "unrelated": ({"pos": "falsifiable", "trivial": "valid"}, False),
    "finite_elements": ({"outside": "falsifiable"}, False),
    "via_function": ({"outside": "unknown"}, True),
    "iset": ({"outside": "falsifiable"}, False),
    "imap": ({"outside": "falsifiable"}, False),
    "iset_from_set": ({"member": "valid", "same": "valid"}, False),
    "refined_first": ({"p": "unknown"}, True),
    "finite_set_ops": ({"inter": "valid", "diff": "valid"}, False),
}


@pytest.mark.parametrize("name", list(models))
def test_finite_sets(tmp_path, name):
    path = tmp_path / f"{name}.lus"
    path.write_text(models[name])
    # A property that holds only of finite sets is not proved: the
    # analysis stops at the timeout
    args = common_args | {"--timeout": "20"}
    arg_list = [arg for pair in args.items() for arg in pair]
    proc = subprocess.run(
        [kind2_bin, "-json", "-v", *arg_list, str(path)],
        capture_output=True,
        text=True,
        timeout=run_timeout,
    )
    output = json.loads(proc.stdout)
    answers = {
        obj["name"]: obj["answer"]["value"]
        for obj in output
        if obj.get("objectType") == "property"
    }
    answers_expected, restart = expected[name]
    assert answers == answers_expected, proc.stdout
    restarted = any(
        obj.get("objectType") == "log" and RESTART_LOG in obj.get("value", "")
        for obj in output
    )
    assert restarted == restart, proc.stdout
    assert not any(
        obj.get("objectType") == "log" and obj.get("level") == "error"
        for obj in output
    ), proc.stdout


# A possibly infinite set or map is not a finite one
type_errors = {
    "assign": """
node main (s: iset<int>) returns (t: set<int>);
let
  t = s;
tel
""",
    "union": """
node main (s: iset<int>) returns (t: set<int>);
let
  t = s + { 1 };
tel
""",
    "argument": """
node f (a: set<int>) returns (b: bool);
let
  b = 0 in a;
tel

node main (s: iset<int>) returns (b: bool);
let
  b = f(s);
tel
""",
    "difference": """
node main (s: set<int>; u: iset<int>) returns (t: set<int>);
let
  t = u - s;
tel
""",
    "map": """
node main (m: imap<int, bool>) returns (n: map<int, bool>);
let
  n = m;
tel
""",
}


@pytest.mark.parametrize("name", list(type_errors))
def test_infinite_containers_are_not_finite(tmp_path, name):
    path = tmp_path / f"{name}.lus"
    path.write_text(type_errors[name])
    proc = subprocess.run(
        [kind2_bin, "-json", str(path)],
        capture_output=True,
        text=True,
        timeout=run_timeout,
    )
    output = json.loads(proc.stdout)
    assert any(
        obj.get("objectType") == "log" and obj.get("level") == "error"
        for obj in output
    ), proc.stdout
