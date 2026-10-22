"""A constant division by zero is left to the solver as an integer division.

The frontend does not fold '7 div 0' or '7 mod 0'; the expression reaches the
term-level evaluators, which used to build a real division ('/') for a 'div'
by a constant zero. The queries were then rejected by the solver ("logic does
not support reals"), and every engine but PDR(IA) failed on the model. The
regression tree only reads exit codes, so the properties being proved by the
one surviving engine hid the failure: this test pins the engines that failed
and checks that no error is reported.
"""

import json
import subprocess

from conftest import common_args, kind2_bin, run_timeout

model = "regression/success/int_div_by_zero_const.lus"


def test_div_by_zero_const_is_an_integer_division():
    args = common_args | {"--timeout": "10"}
    arg_list = [arg for pair in args.items() for arg in pair]
    proc = subprocess.run(
        [kind2_bin, "-json", *arg_list, "--enable", "BMC", "--enable", "IND", model],
        capture_output=True,
        text=True,
        timeout=run_timeout,
    )
    objs = json.loads(proc.stdout)
    errors = [
        obj["value"]
        for obj in objs
        if obj.get("objectType") == "log" and obj.get("level") in ("error", "fatal")
    ]
    assert errors == [], errors
    answers = {
        obj["name"]: obj["answer"]["value"]
        for obj in objs
        if obj.get("objectType") == "property"
    }
    assert answers == {"same_value": "valid", "unconstrained": "valid"}, answers
    assert proc.returncode == 0, proc.returncode
