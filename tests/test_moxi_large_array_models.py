"""The engines read the value of an array from the solver as a whole.

With the theory of arrays, which kmoxi always uses, the solver gives the
value of an array exactly as a term: a constant array with stores. Kind 2
used to read an array element by element instead, over the indices its
bounds give it: 2^w elements for an index of w bits, and kmoxi ran out of
memory in seconds with arrays indexed by 32-bit bit-vectors, as soon as an
engine read a model. The value is now read whole, in a canonical form that
makes equal arrays equal terms, and kmoxi prints it in SMT-LIB syntax, in
the trail and in the :model.

Without the theory of arrays, an array is a function symbol, and its value
is still read element by element, up to SMTSolver.max_array_elements.

The arrays here have 17-bit indices, 2^17 elements: reading them element by
element would be slow rather than too large for memory.
"""

import re
import time

import pytest

from conftest import run_kmoxi_process

sort = "(Array (_ BitVec 17) (_ BitVec 8))"

state = f"""(set-logic QF_ABV)
(define-system main :input ()
  :output ((n (_ BitVec 4)) (a {sort})) :local ()
  :init (= n #x0)
  :trans (and (= n' (bvadd n #x1)) (= a' a)))
(check-system main :input ()
  :output ((n (_ BitVec 4)) (a {sort})) :local ()
  :reachable (r (and (= n #x3) (= (select a #b00000000000000101) #x07)))
  :query (q (r)))
"""

# A constant, whose value is in the :model, and a state variable written to
constant = f"""(set-logic QF_ABV)
(declare-const t {sort})
(define-system main :input ()
  :output ((n (_ BitVec 4)) (a {sort})) :local ()
  :init (and (= n #x0) (= a t))
  :trans (and (= n' (bvadd n #x1))
              (= a' (store a #b00000000000000001 (select a #b00000000000001001)))))
(check-system main :input ()
  :output ((n (_ BitVec 4)) (a {sort})) :local ()
  :reachable (r (and (= n #x2) (= (select t #b00000000000000101) #x07)
                     (= (select a #b00000000000000001) #x03)))
  :query (q (r)))
"""


def run(tmp_path, model, *args):
    path = tmp_path / "model.moxi"
    path.write_text(model)
    start = time.monotonic()
    res = run_kmoxi_process(path, *args, timeout=60)
    # A tenth of a second when the values are read whole; reading the 2^17
    # elements of the arrays one by one takes a minute or more
    elapsed = time.monotonic() - start
    assert elapsed < 20, f"{elapsed:.1f}s: {res.stdout}"
    return res


@pytest.mark.parametrize("engines", [["BMC"], ["IC3QE"], ["IC3IA"], []],
                         ids=["bmc", "ic3qe", "ic3ia", "default"])
def test_state_array(tmp_path, engines):
    res = run(tmp_path, state, *[a for e in engines for a in ("--enable", e)])
    out = res.stdout
    assert ":query (q sat" in out, out + res.stderr
    # The value of the array, whole: a constant array, possibly with stores,
    # with the value the reachability condition reads at index 5. The entry
    # of a is matched from the start of the step, so that only the entry of
    # the step can match it.
    entry = re.compile(r"\s*\(3 \(n \S+\) \(a ")
    steps = [m for m in map(entry.match, out.splitlines()) if m]
    assert len(steps) == 1, out
    step = steps[0].string
    value = step[steps[0].end():]
    assert value.startswith(("(store ", "((as const")), step
    assert f"(as const {sort})" in value and "#b00000111" in value, step


def test_constant_in_model(tmp_path):
    res = run(tmp_path, constant, "--enable", "BMC")
    out = res.stdout
    assert ":query (q sat" in out, out + res.stderr
    model = out.split(":model", 1)[1].split(":trail", 1)[0]
    assert f"(define-fun t () {sort} (store" in model, model
    # The values the reachability condition reads
    assert "#b00000000000000101 #b00000111" in model, model
    assert "#b00000000000001001 #b00000011" in model, model
