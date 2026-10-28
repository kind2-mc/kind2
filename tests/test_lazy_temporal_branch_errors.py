"""The errors for a temporal branch of a lazy construct that cannot be abstracted.

A temporal branch of a lazy construct is abstracted into a call to a generated
node, outside the scope of any quantifier around it, and expanded into one
instance per index of an array comprehension. The branch then cannot mention a
quantified variable, or the index of a comprehension whose size is not
constant, and Kind 2 used to fail an assertion on such a branch (#1757). The
regression tree checks that these programs are rejected; this test checks that
they are rejected for the right reason: a type error in such a branch is still
reported as a type error.
"""

import subprocess

import pytest

from conftest import common_args, kind2_bin, run_timeout

cases = {
    "quantified": ("""
node main (c: bool) returns ();
let
  check forall (k: int) c ==> (true -> k > 0);
tel
""", "Quantified variable 'k' is not allowed in a branch of a lazy construct "
     "that uses a temporal operator"),
    "type_error": ("""
node main (c: bool) returns ();
let
  check forall (k: int) c ==> (true -> k + true > 0);
tel
""", "Expected both arguments of operator to be of same integer, real, or set "
     "types but found int and bool"),
    "symbolic_index": ("""
node main (const n: int; c: bool; a: int^n) returns (b: bool^n);
let
  b = ((c ==> (true -> a[i] > 0)) foreach i < n);
tel
""", "Symbolic array index 'i' is not allowed in a branch of a lazy construct "
     "that uses a temporal operator"),
    "symbolic_index_in_guard": ("""
node main (const n: int; c: bool; a: int^n) returns (b: bool^n);
let
  b = ((a[i] > 0 ==> (true -> c)) foreach i < n);
tel
""", "Symbolic array index 'i' appears in a lazy branch guard, so a temporal "
     "operator in that branch is not allowed"),
    # A pattern variable bound by matching the quantified variable stands for
    # it, but the pass that abstracts the branch does not know it (#1849)
    "quantified_pattern_var": ("""
datatype O = Some (f: bool) | None;
node main (c: bool) returns ();
let
  check forall (k: O) (match k with | Some(v) : c ==> (true -> v) | None : true end);
tel
""", "Pattern variable 'v', bound by matching an expression that depends on "
     "quantified variable 'k', is not allowed in a branch of a lazy construct "
     "that uses a temporal operator"),
    "quantified_pattern_var_node_argument": ("""
datatype O = Some (f: bool) | None;
node N (b: bool) returns (r: bool); let r = b; tel
node main () returns ();
let
  check forall (k: O) (match k with | Some(v) : N(v) | None : true end);
tel
""", "Pattern variable 'v', bound by matching an expression that depends on "
     "quantified variable 'k', is not allowed in an argument of a call to node "
     "or non-inlinable function 'N'"),
}


@pytest.mark.parametrize("case", cases)
def test_lazy_temporal_branch_errors(tmp_path, case):
    model, message = cases[case]
    path = tmp_path / "model.lus"
    path.write_text(model)
    arg_list = [arg for pair in common_args.items() for arg in pair]
    proc = subprocess.run(
        [kind2_bin, *arg_list, str(path)],
        capture_output=True,
        text=True,
        timeout=run_timeout,
    )
    assert proc.returncode == 3, proc.stdout + proc.stderr
    assert message in " ".join((proc.stdout + proc.stderr).split()), proc.stdout + proc.stderr
