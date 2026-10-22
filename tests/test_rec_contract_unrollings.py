"""The number of unrollings a recursive function's contract is proved with.

In the analysis of a recursive function itself, when its contract abstracts
its recursive calls (in a compositional analysis, or for an opaque function),
the contract is the induction hypothesis of the proof of the contract. The
body is unrolled once by default, and --rec_contract_unrollings sets how many
times.

Alt alternates 0 and 1, so its guarantee r >= 0 holds; but assuming it one
level down allows Alt(n - 1) = 2, and then Alt(n) = -1. Two levels down,
Alt(n) = 1 - (1 - Alt(n - 2)) = Alt(n - 2), and the guarantee follows.
"""

import json
import subprocess

from conftest import common_args, kind2_bin, run_timeout

model = """
function rec Alt (n: int) returns (r: int);
(*@contract
  assume n >= 0;
  guarantee "nonneg" r >= 0;
  decreases n;
*)
let
  r = when n = 0 then 0 else 1 - Alt(n - 1);
tel
"""


def answer(tmp_path, extra):
    path = tmp_path / "rec_contract_unrollings.lus"
    path.write_text(model)
    args = common_args | {
        "--compositional": "true",
        "--modular": "true",
        "--timeout": "60",
    } | extra
    arg_list = [arg for pair in args.items() for arg in pair]
    proc = subprocess.run(
        [kind2_bin, "-json", *arg_list, str(path)],
        capture_output=True,
        text=True,
        timeout=run_timeout,
    )
    answers = {
        obj["name"]: obj["answer"]["value"]
        for obj in json.loads(proc.stdout)
        if obj.get("objectType") == "property"
    }
    return proc.returncode, answers


def test_one_unrolling_does_not_prove_it(tmp_path):
    _, answers = answer(tmp_path, {})
    assert answers["nonneg"] != "valid", answers


def test_two_unrollings_prove_it(tmp_path):
    code, answers = answer(tmp_path, {"--rec_contract_unrollings": "2"})
    assert answers["nonneg"] == "valid", answers
    assert code == 0, answers


def test_the_number_must_be_positive(tmp_path):
    path = tmp_path / "rec_contract_unrollings.lus"
    path.write_text(model)
    proc = subprocess.run(
        [kind2_bin, "--rec_contract_unrollings", "0", str(path)],
        capture_output=True,
        text=True,
        timeout=run_timeout,
    )
    assert proc.returncode != 0
    assert "--rec_contract_unrollings" in proc.stdout + proc.stderr
