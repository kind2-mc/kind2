"""The properties of the contract of an imported node in a modular analysis.

An imported node has no implementation, and a modular analysis used to
analyze it on its own only to check its modes. The properties of its
contract, such as the subtype checks of its ghost variables and constants,
were otherwise checked neither there nor in the calling node, which leaves
them to the analysis of the called node in a modular analysis, and a model
that violates them was reported safe (issue #1878). An imported node with
properties of its own is now analyzed on its own, abstracted by its contract,
and they are checked there, once, whether its modes are checked or not. An
imported node without any is still not analyzed on its own.

The contract is assumed in that analysis, guarantees included: slicing the
system to a single property used to drop the definitions of the ghost
variables of an abstract node, which IC3IA, the engine that slices, then
falsified with a spurious counterexample (#1881).

The analysis of an imported node is refined as that of a node with a body:
a check falsified with a callee of its contract abstracted by a contract too
weak for it is proved once the callee is concrete. A monolithic analysis of
an imported node selected with --lus_main checks the same properties.
"""

import json
import subprocess

import pytest

from conftest import common_args, kind2_bin, run_timeout

ghosts = """
type Pos = subtype { x: int | x >= 1 };

function imported F() returns (x: int);
(*@contract
  var l: Pos = 0;
  const c: Pos = 0;
  guarantee x > l;
*)

node N() returns (z: int);
let
  z = F();
  check "P1" z > 0;
tel
"""

# The checks hold by the assumption and the guarantee of the contract
assumed = """
type Pos = subtype { x: int | x >= 1 };

function imported F(y: int) returns (x: int);
(*@contract
  assume y >= 1;
  guarantee x >= 1;
  var l: Pos = x;
  var k: Pos = y;
  mode m (require y > 5;);
  mode n (require y <= 5;);
*)

node N(y: int) returns (z: int);
let
  z = F(1);
tel
"""

# The contract of G is too weak for the subtype check of l
refined = """
type Pos = subtype { x: int | x >= 1 };

function G(y: int) returns (x: int);
(*@contract guarantee true; *)
let
  x = 1;
tel

function imported F(y: int) returns (x: int);
(*@contract var l: Pos = G(y); *)

node N(y: int) returns (z: int);
let
  z = F(y);
tel
"""

plain = """
function imported F(y: int) returns (x: int);
(*@contract
  assume y >= 1;
  guarantee x >= 1;
*)

node N(y: int) returns (z: int);
let
  z = F(1);
  check "P1" z > 0;
tel
"""


def run_kind2(tmp_path, model, *extra, modular="true", json_output=True):
    path = tmp_path / "model.lus"
    path.write_text(model)
    args = common_args | {"--modular": modular}
    arg_list = [arg for pair in args.items() for arg in pair]
    output = ["-json"] if json_output else []
    return subprocess.run(
        [kind2_bin, *output, *arg_list, *extra, str(path)],
        capture_output=True,
        text=True,
        timeout=run_timeout,
    )


def run(tmp_path, model, *extra, modular="true"):
    """The tops of the analyses, in order, and the answers to the properties
    of each analysis"""
    proc = run_kind2(tmp_path, model, *extra, modular=modular)
    analyses = []
    for obj in json.loads(proc.stdout):
        if obj.get("objectType") == "analysisStart":
            analyses.append((obj["top"], {}))
        elif obj.get("objectType") == "property":
            analyses[-1][1][obj["name"]] = obj["answer"]["value"]
    return analyses


def subtypes(answers):
    return {n: v for n, v in answers.items() if "SubType" in n}


@pytest.mark.parametrize("compositional", ["false", "true"])
@pytest.mark.parametrize("check_modes", ["true", "false"])
def test_ghost_subtypes_checked_once(tmp_path, compositional, check_modes):
    analyses = run(
        tmp_path,
        ghosts,
        "--compositional",
        compositional,
        "--check_modes",
        check_modes,
    )
    assert [top for top, _ in analyses] == ["F", "N"], analyses
    assert analyses[0][1] == dict.fromkeys(
        ["SubType[L6C7]", "SubType[L7C3]"], "falsifiable"
    ), analyses
    assert analyses[1][1] == {"P1": "valid"}, analyses


@pytest.mark.parametrize("check_modes", ["true", "false"])
@pytest.mark.parametrize("slicing", ["on", "off"])
def test_contract_assumed(tmp_path, check_modes, slicing):
    analyses = run(
        tmp_path,
        assumed,
        "--enable",
        "IC3IA",
        "--check_modes",
        check_modes,
        "--slice_nodes",
        slicing,
    )
    assert [top for top, _ in analyses] == ["F", "N"], analyses
    assert subtypes(analyses[0][1]) == dict.fromkeys(
        ["SubType[L8C7]", "SubType[L9C7]"], "valid"
    ), analyses
    # The modes are checked only with --check_modes
    assert ("_one_mode_active" in analyses[0][1]) == (check_modes == "true"), (
        analyses
    )
    assert subtypes(analyses[1][1]) == {}, analyses


def test_node_without_props_not_analyzed(tmp_path):
    analyses = run(tmp_path, plain)
    assert [top for top, _ in analyses] == ["N"], analyses


@pytest.mark.parametrize("check_modes", ["true", "false"])
def test_contract_check_refined(tmp_path, check_modes):
    analyses = run(
        tmp_path,
        refined,
        "--compositional",
        "true",
        "--check_modes",
        check_modes,
    )
    assert [top for top, _ in analyses] == ["G", "F", "F"], analyses
    # Falsified with G abstract, proved with G concrete
    assert subtypes(analyses[1][1]) == {"SubType[L11C17]": "falsifiable"}, (
        analyses
    )
    assert subtypes(analyses[2][1]) == {"SubType[L11C17]": "valid"}, analyses


def test_monolithic_main(tmp_path):
    analyses = run(tmp_path, ghosts, "--lus_main", "F", modular="false")
    assert [top for top, _ in analyses] == ["F"], analyses
    assert analyses[0][1] == dict.fromkeys(
        ["SubType[L6C7]", "SubType[L7C3]"], "falsifiable"
    ), analyses


# The summary of the analyses says what the contract check checks
@pytest.mark.parametrize(
    "check_modes, label",
    [("true", "checking mode exhaustiveness"), ("false", "checking contract")],
)
def test_contract_check_label(tmp_path, check_modes, label):
    out = run_kind2(
        tmp_path,
        assumed,
        "--compositional",
        "true",
        "--check_modes",
        check_modes,
        "--color",
        "false",
        json_output=False,
    ).stdout
    labels = [
        line.strip() for line in out.splitlines() if line.strip().startswith("checking")
    ]
    assert labels == [label], out
