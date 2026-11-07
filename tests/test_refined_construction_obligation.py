"""One subtype obligation per record or constructor expression.

A record or constructor expression whose field types carry a refinement is
checked where a constant expression is expected by declaring a constant of
its type: the declared type of that constant yields the obligation. Two
situations used to report the same obligation twice. A construction that is
the whole definition of a constant already declared at its type needs no
constant of its own, since the user's declaration yields the same obligation.
And a construction in the type of an input is met twice, once for the node's
signature and once more while its body re-desugars that type.
"""

import json
import subprocess

import pytest

from conftest import code_to_expected, common_args, kind2_bin, run_timeout

# The construction is the whole definition of a constant of exactly its type
declared_type = """
type R = struct { f: subtype { w: int | w >= 0 } };

node N(x: int) returns (y: int);
const K: R = R { f = 0 };
let
  y = x + K.f;
tel
"""

# The construction is in the type of an input, and the body is desugared too
signature_and_body = """
type R = struct { f: subtype { w: int | w >= 1 } };

node N(r: bool; x: subtype { v: int | v >= (R { f = 2 }).f }) returns (y: int);
let
  restart
    y = 0 -> pre y + x;
  every r end
  check "p" y >= 0;
tel
"""

# The obligations each model is expected to have: the one of the user's own
# declaration for the first, and the one of the construction together with the
# one of the input's refinement at the call for the second
cases = [
    (declared_type, ["SubType[L5C1]"]),
    (signature_and_body, ["SubType[L4C45]", "SubType[L6C3]"]),
]
case_ids = ["declared_type", "signature_and_body"]


@pytest.mark.parametrize("model,expected", cases, ids=case_ids)
def test_one_obligation_per_construction(tmp_path, model, expected):
    path = tmp_path / "refined_construction.lus"
    path.write_text(model)
    args = common_args | {"--timeout": "60"}
    arg_list = [arg for pair in args.items() for arg in pair]
    proc = subprocess.run(
        [kind2_bin, "-json", *arg_list, str(path)],
        capture_output=True,
        text=True,
        timeout=run_timeout,
    )
    assert code_to_expected.get(proc.returncode) == "success", (
        proc.returncode,
        proc.stdout,
        proc.stderr,
    )
    objs = json.loads(proc.stdout)
    subtypes = sorted(
        {
            obj["name"]
            for obj in objs
            if obj.get("objectType") == "property"
            and obj["name"].startswith("SubType")
        }
    )
    assert subtypes == sorted(expected), subtypes
