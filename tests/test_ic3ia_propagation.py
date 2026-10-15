"""IC3IA keeps every cube it propagates in a round.

The propagation phase of IC3IA folds over the cubes of a frame and moves
each that is inductive relative to the frame forward. It used to move a cube
in the frames the round was entered with, which undid the earlier moves of
the round, while the later queries of the round had already used those
moves: a cube could end up two frames ahead of a cube its proof relied on,
and when the frame in between was found empty, the frames after it were
reported as an inductive invariant that was not. On the model below, the
state is reachable in 8 steps and IC3IA answered unsat with a certificate
that was not inductive (#1801).
"""

import shutil

import pytest

from conftest import ic3ia_args, ic3ia_solver, run_kmoxi

model = """(set-logic QF_BV)
(define-system main
 :input ((i0 Bool))
 :output ((s0 Bool) (s1 Bool) (s2 Bool) (s3 Bool) (s4 Bool) (s5 Bool) (s6 Bool))
 :local ()
 :init (and (not s0) (not s1) s2 (not s3) s4 s5 (not s6))
 :trans (and (= s0' s1) (= s1' (not s4)) (= s2' (xor s2 (and s1 s0)))
             (= s3' (not (or (xor s1 s5) (ite (not s0) s6 s4))))
             (= s4' (xor s4 (and s3 s2)))
             (= s5' (not (ite (not i0) (not s6) s4)))
             (= s6' (xor s0 (not i0))))
 :inv true)
(check-system main
 :input ((i0 Bool))
 :output ((s0 Bool) (s1 Bool) (s2 Bool) (s3 Bool) (s4 Bool) (s5 Bool) (s6 Bool))
 :local ()
 :reachable (r (and (not s5) (not s4) (not s3) s0 (not s6) (not s2) s1))
 :query (q (r)))
"""


@pytest.mark.skipif(
    shutil.which(ic3ia_solver) is None, reason=f"{ic3ia_solver} is not installed"
)
def test_ic3ia_finds_the_reachable_state(tmp_path):
    path = tmp_path / "model.moxi"
    path.write_text(model)
    args = [arg for pair in ic3ia_args.items() for arg in pair]
    out, err = run_kmoxi(path, *args)
    assert ":query (q sat" in out, out + err
