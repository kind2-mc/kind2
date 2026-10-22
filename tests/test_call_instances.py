"""The properties lifted from the instances of an expanded call stay distinct.

A call in an array comprehension expands into one instance per index, and all of
them share the position of the call. Property statuses are matched by name, so
if the names of the properties lifted from the instances only carried that
position, the instances would share one status, decided by whichever engine
reported first (#1514). The exit code does not tell that apart from a correct
run, so this checks the status of each instance. The node generated for a
restart (Main7, Main10) does not show in the names of its properties: the
indices of its instances go to the first call in the name.
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
    # Main1: s = (Sub(a[i]) foreach i)^3
    **{f"Sub[L19C8][{i}].assume[L8C3]": i == 0 for i in range(3)},
    # Main2: s = (Sub(a[i][j]) foreach i, j)^2^3
    **{
        f"Sub[L29C8][{i}][{j}].assume[L8C3]": (i, j) == (1, 0)
        for i in range(3)
        for j in range(2)
    },
    # Main3: s = (Mid(a[m], k)[k] foreach m, k)^2^3, with
    # r = (Sub(b[k]) foreach k)^2 in Mid
    **{
        f"Mid[L48C8][{m}][{k}].Sub[L41C8][{n}].assume[L8C3]": (m, n) == (2, 0)
        for m in range(3)
        for k in range(2)
        for n in range(2)
    },
    # Main4: s = (Mid(a[m], 0)[k] foreach m, k)^2^3, whose call does not
    # depend on k
    **{
        f"Mid[L62C8][{m}].Sub[L41C8][{n}].assume[L8C3]": (m, n) == (2, 0)
        for m in range(3)
        for n in range(2)
    },
    # Main5: s = (Wrap(Sub(a[i])) foreach i)^3. The assumption of Wrap always
    # holds: it checks the indices of the instances of the outer call
    **{f"Sub[L83C13][{i}].assume[L8C3]": i == 1 for i in range(3)},
    **{f"Wrap[L83C8][{i}].assume[L73C3]": False for i in range(3)},
    # Main6: s = (Wrap(when m = i then Sub(a[i]) else 0) foreach i)^3
    **{f"Sub[L95C29][{i}].assume[L8C3]": i == 2 for i in range(3)},
    **{f"Wrap[L95C8][{i}].assume[L73C3]": False for i in range(3)},
    # Main7: s = (restart Wrap(a[i]) every Pos(Sub(a[i])) foreach i)^3
    **{f"Sub[L111C37][{i}].assume[L8C3]": i == 1 for i in range(3)},
    **{f"Wrap[L111C16][{i}].assume[L73C3]": False for i in range(3)},
    # Main8: s = (Wrap(Sub(a[i][j])) foreach i, j)^2^3
    **{
        f"Sub[L122C13][{i}][{j}].assume[L8C3]": (i, j) == (1, 1)
        for i in range(3)
        for j in range(2)
    },
    **{
        f"Wrap[L122C8][{i}][{j}].assume[L73C3]": False
        for i in range(3)
        for j in range(2)
    },
    # Main9: s = (Wrap(Wrap(Sub(a[i]))) foreach i)^3
    **{f"Sub[L133C18][{i}].assume[L8C3]": i == 2 for i in range(3)},
    **{f"Wrap[L133C13][{i}].assume[L73C3]": False for i in range(3)},
    **{f"Wrap[L133C8][{i}].assume[L73C3]": False for i in range(3)},
    # Main10: s = (restart Wrap(Sub(a[i])) every r foreach i)^3
    **{f"Sub[L144C21][{i}].assume[L8C3]": i == 1 for i in range(3)},
    **{f"Wrap[L144C16][{i}].assume[L73C3]": False for i in range(3)},
    # Main11: s = (restart (Sub(a[i][j]) foreach j)^2 every r foreach i)^3
    **{
        f"Sub[L156C17][{i}][{j}].assume[L8C3]": (i, j) == (1, 1)
        for i in range(3)
        for j in range(2)
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
