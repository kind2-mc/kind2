"""A call that does not depend on the index variable of a comprehension is made once.

A call in an array comprehension that takes an index variable expands into one
instance per index. A call of the same equation whose operands do not mention
that variable, and that is under no lazy construct whose condition does, takes
the same value at every index, and used to be expanded all the same, into
identical instances, including when it was an operand of a call that takes the
index variable, or in the condition of a lazy construct that mentions it. Those
instances each brought a copy of the callee and of its properties (#1755). The
verdicts do not tell that apart, so this checks the names of the properties
lifted from the instances.
"""

import json
import subprocess
from pathlib import Path

from conftest import common_args, kind2_bin, run_timeout

model = (
    Path(__file__).parent
    / "regression"
    / "success"
    / "comprehension_index_independent_call.lus"
)

expected = {
    # A = (if F() = 1 then G(i) else 0 foreach i)^3
    "F[L25C11].f",
    *(f"G[L25C24][{i}].g" for i in range(3)),
    # B = (when F() = 1 then G(i) else 0 foreach i)^3
    "F[L27C13].f",
    *(f"G[L27C26][{i}].g" for i in range(3)),
    # C = (G(G(m)) + G(i) foreach i)^3
    "G[L29C8].g",
    "G[L29C10].g",
    *(f"G[L29C18][{i}].g" for i in range(3)),
    # D = (when m = i then G(m) else 0 foreach i)^3
    *(f"G[L32C24][{i}].g" for i in range(3)),
    # E = (G(j) + G(m) foreach i, j)^2^3
    *(f"G[L34C8][{j}].g" for j in range(2)),
    "G[L34C15].g",
    # P = (H(F(), i) foreach i)^3
    "F[L36C10].f",
    # Q = (when F() = 1 and m = i then G(i) else 0 foreach i)^3
    "F[L39C13].f",
    *(f"G[L39C36][{i}].g" for i in range(3)),
    # The calls of F in the checks of main
    "F[L40C24].f",
    "F[L41C24].f",
    "F[L45C20].f",
    "F[L46C24].f",
    # The checks of main
    "A",
    "B",
    "C",
    "D",
    "E",
    "P",
    "Q",
}


def test_index_independent_call_made_once():
    arg_list = [arg for pair in common_args.items() for arg in pair]
    run = subprocess.run(
        [kind2_bin, "-json", *arg_list, str(model)],
        capture_output=True,
        text=True,
        timeout=run_timeout,
    )
    answers = {
        obj["name"]: obj["answer"]["value"]
        for obj in json.loads(run.stdout)
        if obj.get("objectType") == "property"
    }
    assert answers == {name: "valid" for name in expected}
