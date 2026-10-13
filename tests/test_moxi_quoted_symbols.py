"""kmoxi quotes the symbols of its responses when needed.

The names of the variables, systems, conditions, queries and what is named
after them, constants, enumeration sorts and values are printed as quoted
symbols when they are not simple symbols. The solvers are given the
predicates of a system whose name needs quoting under a simple symbol;
they used to reject them.
"""

import subprocess

import pytest

from conftest import kill_tree, kmoxi_args, kmoxi_bin


def run(tmp_path, model, extra, env=None, timeout=60):
    if not kmoxi_bin.exists():
        pytest.skip(f"{kmoxi_bin} is not built (make kmoxi)")
    path = tmp_path / "model.moxi"
    path.write_text(model)
    args = kmoxi_args | {"--timeout": "30"}
    arg_list = [arg for pair in args.items() for arg in pair]
    proc = subprocess.Popen(
        [kmoxi_bin, *arg_list, *extra, str(path)],
        stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True,
        start_new_session=True, env=env,
    )
    try:
        stdout, stderr = proc.communicate(timeout=timeout)
    except subprocess.TimeoutExpired:
        kill_tree(proc)
        proc.communicate()
        pytest.fail(f"no answer after {timeout}s")
    return proc.returncode, stdout, stderr


quoted = """(set-logic QF_LIA)
(declare-enum-sort |traffic light| (|go now| stop))
(declare-const |my k| Int)
(define-system |the sys| :input () :output ((|x y| Int) (l |traffic light|))
  :local ((|2t| Int))
  :init (and (= |x y| 0) (= |2t| 0) (= l |go now|))
  :trans (and (= |x y|' (+ |x y| |my k|)) (= |2t|' (+ |2t| 1)) (= l' stop)))
(check-system |the sys| :input () :output ((|x y| Int) (l |traffic light|))
  :local ((|2t| Int))
  :reachable (|reach it| (and (= |2t| 2) (= |x y| 4) (= l stop)))
  :query (|q 1| (|reach it|)))
"""


def test_symbols_quoted(tmp_path):
    _, out, err = run(tmp_path, quoted, ["--enable", "BMC"])
    for text in [
        ":query (|q 1| sat :model |q 1_model| :trace |q 1_trace|)",
        ":trace (|q 1_trace| :prefix |q 1_prefix|)",
        "(define-fun |my k| () Int 2)",
        "(|the sys|::|x y| 0) (|the sys|::l |go now|) (|the sys|::|2t| 0)",
        "(|reach it| true)",
    ]:
        assert text in out, out + err
    # Simple symbols are not quoted
    assert "|l|" not in out and "|stop|" not in out, out
