"""The properties lifted from the instances of an expanded call stay distinct.

A call in an array equation expands into one instance per index, and all of
them share the position of the call. Property statuses are matched by name, so
if the names of the properties lifted from the instances only carried that
position, the instances would share one status, decided by whichever engine
reported first (#1514). The exit code does not tell that apart from a correct
run, so this checks the status of each instance.
"""

import json
import subprocess
from pathlib import Path

from conftest import common_args, kind2_bin, run_timeout

model = (
    Path(__file__).parent
    / "regression"
    / "falsifiable"
    / "array_call_instance_props.lus"
)

# The assumption properties of the model, by name, and whether each is
# falsifiable
expected = {
    # Main1: s[i] = Sub(a[i])
    **{f"Sub[L19C10][{i}].assume[L8C3]": i == 0 for i in range(3)},
    # Main2: s[i][j] = Sub(a[i][j])
    **{
        f"Sub[L29C13][{i}][{j}].assume[L8C3]": (i, j) == (1, 0)
        for i in range(3)
        for j in range(2)
    },
    # Main3: s[m][k] = Mid(a[m])[k], with r[k] = Sub(b[k]) in Mid
    **{
        f"Mid[L48C13][{m}][{k}].Sub[L41C10][{n}].assume[L8C3]": (m, n) == (2, 0)
        for m in range(3)
        for k in range(2)
        for n in range(2)
    },
}


def test_instances_have_their_own_status():
    arg_list = [arg for pair in common_args.items() for arg in pair]
    run = subprocess.run(
        [kind2_bin, "-json", *arg_list, str(model)],
        capture_output=True,
        text=True,
        timeout=run_timeout,
    )
    answers = [
        (obj["name"], obj["answer"]["value"])
        for obj in json.loads(run.stdout)
        if obj.get("objectType") == "property" and obj.get("source") == "Assumption"
    ]
    names = [name for name, _ in answers]
    assert len(names) == len(set(names)), "instances share a property name"
    assert dict(answers) == {
        name: "falsifiable" if falsifiable else "valid"
        for name, falsifiable in expected.items()
    }
