"""With --lus_push_pre, 'pre' applied to a when-then-else expression is kept.

push_pre returned 'when c then e1 else e2' unchanged when applied to it,
dropping the 'pre'. Here q is 'pre r' after the first step, so the property
is valid; with the 'pre' dropped, q equals r and the property is falsified
after one step.
"""

import json
import subprocess

import pytest

from conftest import common_args, kind2_bin, run_timeout

model = """
node top (c: bool) returns (r, q: bool);
let
  r = when c then (true -> not pre r) else false;
  q = false -> pre (when c then (true -> not pre r) else false);
  check "q_is_pre_r" q = (false -> pre r);
tel
"""


@pytest.mark.parametrize("push_pre", ["false", "true"])
def test_push_pre_keeps_pre_of_lazy_ite(tmp_path, push_pre):
    path = tmp_path / "model.lus"
    path.write_text(model)
    args = common_args | {
        "--timeout": "10",
        "--lus_push_pre": push_pre,
    }
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
    assert answers.get("q_is_pre_r") == "valid", answers
