"""kmoxi reports the check-system attributes it does not translate.

The attributes :current, :fairness and :queries are parsed and type
checked; kmoxi used to reject them as an unexpected character. An
initiality condition is a one-state formula, at most one per query, and a
fairness condition may prime inputs only. A query that names a :current or
:fairness condition, or a check-system with several queries, is reported as
unsupported, at the condition or command; so is a query with several
:reachable conditions, at the second one. A condition that no query names
is ignored, as it does not change the query.
"""

import subprocess

import pytest

from conftest import kill_tree, kmoxi_args, kmoxi_bin

# Exit code of a parse or type error
PARSE_ERROR = 3

head = """(set-logic QF_LIA)
(define-system main :input ((i Int)) :output ((n Int)) :local ()
  :init (= n 0) :trans (= n' (+ n (ite (> i' 0) 2 0))))
(check-system main :input ((i Int)) :output ((n Int)) :local ()
"""


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


unsupported = {
    "current": (
        "  :current (c (= n 1)) :reachable (r (> n 3)) :query (q (c r)))\n",
        "5:13", "kmoxi does not support :current conditions",
    ),
    # A query may name its :current condition more than once
    "current named twice": (
        "  :current (c (= n 1)) :reachable (r (> n 3)) :query (q (c c r)))\n",
        "5:13", "kmoxi does not support :current conditions",
    ),
    "fairness": (
        "  :fairness (f (> i' 0)) :reachable (r (> n 3)) :query (q (f r)))\n",
        "5:14", "kmoxi does not support :fairness conditions",
    ),
    "queries": (
        "  :reachable (r (> n 3)) :reachable (s (< n 0))\n"
        "  :queries ((q1 (r)) (q2 (s))))\n",
        "4:1", "kmoxi supports one :query per check-system",
    ),
    "several reachable": (
        "  :reachable (r (> n 3)) :reachable (s (< n 0)) :query (q (r s)))\n",
        "5:38", "kmoxi supports one :reachable condition per query",
    ),
}


@pytest.mark.parametrize("case", unsupported, ids=unsupported)
def test_unsupported_reported(tmp_path, case):
    attrs, position, message = unsupported[case]
    code, _, _ = run(tmp_path, head + attrs, ["--only_parse", "true"])
    assert code == 0
    code, out, err = run(tmp_path, head + attrs, [])
    assert code == PARSE_ERROR, out + err
    assert f"model.moxi:{position}: error: {message}" in out, out
    assert out.startswith('(error "') and out.endswith('")\n'), out
    assert err == "", err


ill_typed = {
    "two current": (
        "  :current (c1 (= n 1)) :current (c2 (= n 2)) :reachable (r (> n 3))\n"
        "  :query (q (c1 c2 r)))\n",
        "6:17", "query q names more than one :current condition",
    ),
    "primed current": (
        "  :current (c (= n' 1)) :reachable (r (> n 3)) :query (q (c r)))\n",
        "5:18", "next-state variable n' in the :current condition c",
    ),
    "fairness primes a non-input": (
        "  :fairness (f (> n' 0)) :reachable (r (> n 3)) :query (q (f r)))\n",
        "5:19", "next-state variable n' in the :fairness condition f, where only "
        "input variables may be primed",
    ),
}


@pytest.mark.parametrize("case", ill_typed, ids=ill_typed)
def test_ill_typed_conditions(tmp_path, case):
    attrs, position, message = ill_typed[case]
    code, out, err = run(tmp_path, head + attrs, ["--only_parse", "true"])
    assert code == PARSE_ERROR, out + err
    assert f"model.moxi:{position}: error: {message}" in out, out
    assert out.startswith('(error "') and out.endswith('")\n'), out
    assert err == "", err


# Answered queries: conditions no query names are ignored, and a :queries
# attribute with one query is a :query
answered = {
    "unnamed current":
        "  :current (c (= n 1)) :reachable (r (= n 4)) :query (q (r)))\n",
    "unnamed fairness":
        "  :fairness (f (> i' 0)) :reachable (r (= n 4)) :query (q (r)))\n",
    "one query in queries":
        "  :reachable (r (= n 4)) :queries ((q (r))))\n",
    "reachable named twice":
        "  :reachable (r (= n 4)) :query (q (r r)))\n",
}


@pytest.mark.parametrize("case", answered, ids=answered)
def test_answered(tmp_path, case):
    code, out, err = run(tmp_path, head + answered[case], ["--enable", "BMC"])
    assert code == 0 and ":query (q :result sat" in out, out + err
