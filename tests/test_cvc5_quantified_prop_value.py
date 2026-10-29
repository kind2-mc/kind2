"""A valid quantified property is not falsified along with another property
of the node (#1816).

A property is defined by a state variable, `(= p (forall ...))`. cvc5
eliminates such a variable during preprocessing, and when the query is
satisfied whatever its value -- here, because the other property is
falsified -- it never decides the quantified formula. Up to 1.3.0, get-value
then returned the formula itself rather than a value; Kind 2 took anything
but `true` for a falsified property, and reported the valid property invalid
from the counterexample of the other one.

cvc5 1.3.1 and later compute such values with a subsolver, unless given
--no-check-model-subsolver. A wrapper passes that option when the installed
cvc5 has it, so that the behavior of 1.3.0 is reproduced whatever the
version.
"""

import json
import shutil
import subprocess
import sys

import pytest

from conftest import common_args, kind2_bin, run_timeout

model = """
node main(c: bool) returns ();
let
  check "P1" not c;
  check "P2" forall (x: int) (x > 2 and x < 4) ==> x = 3;
tel
"""

cvc5 = shutil.which("cvc5")


def without_subsolver_option():
    """The option that turns off the subsolver of get-value, if the
    installed cvc5 has it"""
    option = "--no-check-model-subsolver"
    probe = subprocess.run(
        [cvc5, option, "--version"], capture_output=True, timeout=30
    )
    return [option] if probe.returncode == 0 else []


@pytest.mark.skipif(cvc5 is None, reason="needs cvc5")
@pytest.mark.skipif(
    sys.platform == "win32",
    reason="needs a POSIX shell to pass cvc5 an extra option",
)
@pytest.mark.parametrize(
    "engines",
    [["--enable", "BMC"], ["--enable", "BMC", "--enable", "IND"]],
    ids=["bmc", "bmc_ind"],
)
def test_cvc5_quantified_prop_value(tmp_path, engines):
    path = tmp_path / "model.lus"
    path.write_text(model)
    wrapper = tmp_path / "cvc5"
    wrapper.write_text(
        "#!/bin/sh\n"
        f'exec "{cvc5}" {" ".join(without_subsolver_option())} "$@"\n'
    )
    wrapper.chmod(0o755)

    # BMC alone never proves P2, and stops at the timeout
    args = common_args | {"--timeout": "5"}
    arg_list = [arg for pair in args.items() for arg in pair]
    proc = subprocess.run(
        [
            kind2_bin, "-json", *arg_list,
            "--smt_solver", "cvc5", "--cvc5_bin", str(wrapper),
            *engines, str(path),
        ],
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
    assert answers.get("P1") == "falsifiable", proc.stdout
    assert answers.get("P2") != "falsifiable", proc.stdout
    if "IND" in engines:
        assert answers.get("P2") == "valid", proc.stdout
    assert not any(
        obj.get("objectType") == "log" and obj.get("level") == "error"
        for obj in output
    ), proc.stdout
