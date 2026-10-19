"""kmoxi registers the flags that concern it, and no other.

kind2 and kmoxi share their flags, and kmoxi used to register all of them:
its usage message spoke of a Lustre program, --help_of listed the contract,
certificate and test-generation modules, and a Lustre-only flag such as
--lus_main was accepted and ignored. Each executable now parses the command
line under a profile: kmoxi shows and accepts the engine, solver and theory
flags, and the global flags that are not about the Lustre front end; the
others are unknown to it. kind2 is unchanged.
"""

import re
import subprocess

import pytest

from conftest import kind2_bin, kmoxi_bin, run_timeout, query_answer

model = """
(set-logic QF_LIA)
(define-system main :input () :output ((x Int)) :local ()
  :init (= x 0) :trans (= x' (+ x 1)))
(check-system main :input () :output ((x Int)) :local ()
  :reachable (rch (= x 3)) :query (q (rch)))
"""


def run(binary, args):
    if not binary.exists():
        pytest.skip(f"{binary} is not built")
    res = subprocess.run(
        [binary, *args], capture_output=True, text=True, timeout=run_timeout
    )
    plain = re.sub(r"\x1b\[[0-9;]*m", "", res.stdout + res.stderr)
    return res.returncode, plain


def test_kmoxi_usage_describes_moxi():
    _, out = run(kmoxi_bin, ["--help"])
    assert "MoXI model" in out, out
    assert "Lustre" not in out, out
    # The global flags kmoxi keeps, and the ones it does not
    for flag in ("--timeout", "--enable", "--color", "--only_parse"):
        assert flag in out, flag
    for flag in ("--lus_main", "--modular", "--slice_nodes", "--input_format"):
        assert flag not in out, flag


def test_kind2_usage_unchanged():
    _, out = run(kind2_bin, ["--help"])
    assert "Lustre program" in out, out
    assert "--lus_main" in out, out


def test_kmoxi_modules():
    _, out = run(kmoxi_bin, ["--help_of", "all"])
    for module in ("smt", "ind", "ic3qe", "ic3ia", "invgen", "c2i", "arrays"):
        assert f"Module {module}:" in out, module
    for module in ("contracts", "certif", "ivc", "mcs", "test", "lsp"):
        assert f"Module {module}:" not in out, module
    # The legal values of --help_of are the modules of the profile, in its
    # description and in its check, which rejects the others when parsing
    _, out = run(kmoxi_bin, ["--help"])
    assert re.search(r"^\s+c2i\s", out, re.M), out
    assert not re.search(r"^\s+contracts\s", out, re.M), out
    code, out = run(kmoxi_bin, ["--help_of", "contracts"])
    assert code != 0 and 'unknown module identifier ""contracts""' in out, out
    _, out = run(kind2_bin, ["--help_of", "contracts"])
    assert "Module contracts:" in out, out


def test_kmoxi_rejects_kind2_only_flag(tmp_path):
    path = tmp_path / "counter.moxi"
    path.write_text(model)
    code, out = run(kmoxi_bin, ["--lus_main", "main", str(path)])
    assert code != 0 and out == '(error "unknown flag --lus_main")\n', out
    # A flag kmoxi keeps still parses: the run goes on to the analysis, and
    # BMC finds the state at depth 3
    code, out = run(kmoxi_bin, ["--timeout", "20", "--enable", "BMC", str(path)])
    assert code == 0 and query_answer(out) == "sat", out
    # C2I runs on MoXI systems, so its flags are registered
    code, out = run(
        kmoxi_bin,
        ["--timeout", "20", "--enable", "BMC", "--enable", "C2I", "--c2i_dnf", "2", str(path)],
    )
    assert code == 0 and query_answer(out) == "sat", out
