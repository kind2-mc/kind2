"""kmoxi translates every bit-vector operator of SMT-LIB.

Kind 2 has symbols for most of the FixedSizeBitVectors theory, but not for
bvnand, bvnor, bvxnor, bvcomp, bvsmod, repeat, rotate_left and rotate_right,
and the MoXI front end translated neither these nor sign_extend and
zero_extend, for which Kind 2 does have symbols: a model using one was
rejected as unsupported. bvsmod now has a symbol of its own, since its
definition repeats its operands and nesting it made the queries grow
exponentially; the others are defined from the operators Kind 2 has, as the
theory defines them, each mentioning its operands once. Each operator is checked against an independent
formulation of its meaning, over symbolic 8-bit inputs where SMT-LIB gives
one (the shifts for the rotations, the sign test for the sign extension),
and against the values z3 computes otherwise (the signed modulo, whose sign
follows the divisor, and a corner case of each definition). Every query here
is unsatisfiable, except the last, which checks that the operators are not
trivially translated: a rotation can reach a given value.
"""

import subprocess

import pytest

from conftest import common_args, kmoxi_bin, run_timeout

system = """
(set-logic QF_BV)
(define-system main
  :input ((x (_ BitVec 8)) (y (_ BitVec 8))) :output ((o Bool)) :local ()
  :inv (= o true))
(check-system main
  :input ((x (_ BitVec 8)) (y (_ BitVec 8))) :output ((o Bool)) :local ()
  :reachable (r {condition})
  :query (q (r)))
"""

# The identities, each negated into a reachability condition expected unsat
identities = {
    "zero_extend": "(= ((_ zero_extend 4) x) (concat #x0 x))",
    "zero_extend-0": "(= ((_ zero_extend 0) x) x)",
    "sign_extend": "(= ((_ sign_extend 4) x) (ite (bvslt x #x00) (concat #xF x) (concat #x0 x)))",
    "sign_extend-value": "(= ((_ sign_extend 4) #xF9) #xFF9)",
    "repeat": "(= ((_ repeat 3) x) (concat x (concat x x)))",
    "repeat-1": "(= ((_ repeat 1) x) x)",
    "rotate_left": "(= ((_ rotate_left 3) x) (bvor (bvshl x #x03) (bvlshr x #x05)))",
    "rotate_left-wrap": "(= ((_ rotate_left 11) x) ((_ rotate_left 3) x))",
    "rotate_left-value": "(= ((_ rotate_left 3) #x81) #x0C)",
    "rotate_right": "(= ((_ rotate_right 3) x) (bvor (bvlshr x #x03) (bvshl x #x05)))",
    "rotate_right-full": "(= ((_ rotate_right 16) x) x)",
    "rotate_right-value": "(= ((_ rotate_right 3) #x81) #x30)",
    "bvnand": "(= (bvnand x y) (bvnot (bvand x y)))",
    "bvnor": "(= (bvnor x y) (bvnot (bvor x y)))",
    "bvxnor": "(= (bvxnor x y) (bvnot (bvxor x y)))",
    "bvcomp": "(= (bvcomp x y) (ite (= x y) #b1 #b0))",
    # bvsmod: the sign of the result is the sign of the divisor, and
    # s = t * q + r for the rounding-down quotient; values from z3
    "bvsmod-values": "(and (= (bvsmod #xF9 #x03) #x02) (= (bvsmod #x07 #xFD) #xFE)"
    " (= (bvsmod #xF9 #xFD) #xFF) (= (bvsmod #x07 #x03) #x01) (= (bvsmod #x80 #xFF) #x00)"
    " (= (bvsmod #x07 #x00) #x07) (= (bvsmod #xF9 #x00) #xF9))",
    "bvsmod-by-zero": "(= (bvsmod x #x00) x)",
    "bvsmod-sign": "(=> (and (not (= y #x00)) (not (= (bvsmod x y) #x00)))"
    " (= (bvslt (bvsmod x y) #x00) (bvslt y #x00)))",
    # Nested bvsmod stays linear in size: a native symbol, not an expansion
    "bvsmod-nested": "(=> (not (= y #x00)) (let ((r (bvsmod (bvsmod (bvsmod (bvsmod (bvsmod"
    " (bvsmod x y) y) y) y) y) y))) (bvult (ite (bvslt r #x00) (bvneg r) r)"
    " (ite (bvslt y #x00) (bvneg y) y))))",
    # A wide repeat is built by doubling
    "repeat-wide": "(= ((_ extract 8199 8192) ((_ repeat 4096) x)) x)",
    "bvsmod-magnitude": "(=> (not (= y #x00)) (bvult (ite (bvslt (bvsmod x y) #x00)"
    " (bvneg (bvsmod x y)) (bvsmod x y)) (ite (bvslt y #x00) (bvneg y) y)))",
}


def run(tmp_path, condition):
    path = tmp_path / "bv.moxi"
    path.write_text(system.format(condition=condition))
    args = common_args | {"--timeout": "30"}
    arg_list = [arg for pair in args.items() for arg in pair]
    return subprocess.run(
        [kmoxi_bin, *arg_list, "--enable", "BMC", "--enable", "IND", str(path)],
        capture_output=True,
        text=True,
        timeout=run_timeout,
    )


@pytest.mark.parametrize("name", identities, ids=list(identities))
def test_operator_has_its_smtlib_meaning(tmp_path, name):
    if not kmoxi_bin.exists():
        pytest.skip(f"{kmoxi_bin} is not built (make kmoxi)")

    result = run(tmp_path, f"(not {identities[name]})")
    assert ":query (q unsat" in result.stdout, result.stdout + result.stderr


def test_operator_is_translated(tmp_path):
    if not kmoxi_bin.exists():
        pytest.skip(f"{kmoxi_bin} is not built (make kmoxi)")

    result = run(tmp_path, "(= ((_ rotate_left 1) (bvnand x y)) #x01)")
    assert ":query (q sat" in result.stdout, result.stdout + result.stderr
