"""Array literals that mention the index variable of an array comprehension.

Such a literal is abstracted to a local defined element by element over the
index variable (issue #1748). Each false property is checked to be falsified
on its own, so that a definition of the local that over-constrains it, and
makes a false property valid, is caught; the valid properties are checked
alongside, so that one that under-constrains it is caught as well.
"""

import json
import subprocess

from conftest import common_args, kind2_bin, run_timeout

model = """
node main (B: int^3) returns (A: int^2^3; S: int^3; U: int^3);
let
  A = ([i, B[i]] foreach i)^3;
  S = (0 -> (pre [i, B[i]])[B[i] mod 2] foreach i)^3;
  U = ([i, B[i]][B[i] mod 2] + [i, B[i]][(B[i] + 1) mod 2] foreach i)^3;

  check "a_valid" A[2][0] = 2 and A[1][1] = B[1];
  check "s_valid" true -> (B[1] mod 2 = 0 => S[1] = 1);
  check "u_valid" U[1] = 1 + B[1];

  -- B[1] is not bounded by the range of the index variable
  check "a_elem_in_range" A[1][1] < 3;
  check "a_elem_zero" A[1][1] = 0;
  check "s_zero" S[1] = 0;
  check "u_index" U[1] = 2;
tel
"""

expected = {
    "a_valid": "valid",
    "s_valid": "valid",
    "u_valid": "valid",
    "a_elem_in_range": "falsifiable",
    "a_elem_zero": "falsifiable",
    "s_zero": "falsifiable",
    "u_index": "falsifiable",
    # The reads of the literals at B[i] mod 2 and (B[i] + 1) mod 2, which are
    # within the bounds of a literal of two elements
    "ArrayBounds[L5C29]": "valid",
    "ArrayBounds[L6C18]": "valid",
    "ArrayBounds[L6C42]": "valid",
}


def test_array_literal_index_var(tmp_path):
    path = tmp_path / "model.lus"
    path.write_text(model)
    args = common_args | {"--timeout": "20"}
    arg_list = [arg for pair in args.items() for arg in pair]
    proc = subprocess.run(
        [kind2_bin, "-json", *arg_list, str(path)],
        capture_output=True,
        text=True,
        timeout=run_timeout,
    )
    objs = json.loads(proc.stdout)
    answers = {
        obj["name"]: obj["answer"]["value"]
        for obj in objs
        if obj.get("objectType") == "property"
    }
    assert answers == expected, answers
