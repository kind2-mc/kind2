"""A call relies on a temporal function contract while its assumptions have
held.

The guarantees of a function whose contract has no state only depend on the
current values of the streams, and a call relies on them when the assumptions
hold at the current instant. Those of a contract with temporal operators may
depend on the assumptions at the previous instants, as the guarantees of a
node do. A call used to rely on them when the assumptions held at the current
instant only, and a property of a caller that violated the assumptions at an
earlier instant could be proved although it is false. The assumption is
falsified in any case, and the exit code counts every analysis, so this checks
that the property is never proved.
"""

import json
import subprocess
from pathlib import Path

from conftest import common_args, kind2_bin, run_timeout

model = (
    Path(__file__).parent
    / "regression"
    / "falsifiable"
    / "compositional"
    / "function_temporal_contract_assumption_history.lus"
)


def test_false_property_not_proved():
    args = common_args | {"--compositional": "true"}
    arg_list = [arg for pair in args.items() for arg in pair]
    run = subprocess.run(
        [kind2_bin, "-json", *arg_list, str(model)],
        capture_output=True,
        text=True,
        timeout=run_timeout,
    )

    answers = []
    top = None
    for obj in json.loads(run.stdout):
        if obj.get("objectType") == "analysisStart":
            top = obj["top"]
        elif (
            obj.get("objectType") == "property"
            and top == "main"
            and obj.get("name") == "ok"
        ):
            answers.append(obj["answer"]["value"])

    assert answers, run.stdout
    assert "valid" not in answers, run.stdout
