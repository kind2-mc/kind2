"""IC3 is a virtual module that stands for both IC3QE and IC3IA.

Enabling IC3 enabled both engines, but disabling IC3 disabled neither: the
disabled modules were removed from the enabled ones as given, and IC3 is
never one of the enabled modules by default. A run with --disable IC3 still
ran both engines. Likewise, --enable IC3 --disable IC3IA still ran IC3IA.

The engines a run uses are listed in its verbose output. The property is
falsified at once by every engine, so that each run stops right away.
"""

import subprocess

import pytest

from conftest import common_args, kind2_bin, run_timeout

model = """
node main (x: int) returns (y: int);
let
  y = x;
  check x <> 0;
tel
"""

pdr_qe = "property directed reachability (QE)"
pdr_ia = "property directed reachability (IA)"
bmc = "bounded model checking"


def engines(path, flags):
    args = common_args | {"--timeout": "20"}
    arg_list = [arg for pair in args.items() for arg in pair]
    run = subprocess.run(
        [kind2_bin, "-v", *arg_list, *flags, str(path)],
        capture_output=True,
        text=True,
        timeout=run_timeout,
    )
    lines = run.stdout.splitlines()
    start = next(
        i for i, line in enumerate(lines) if "Running in parallel mode:" in line
    )
    names = []
    for line in lines[start:]:
        if "- " not in line:
            break
        names.append(line.split("- ", 1)[1].strip())
    return set(names)


@pytest.mark.parametrize(
    "flags, present, absent",
    [
        (["--disable", "IC3"], {bmc}, {pdr_qe, pdr_ia}),
        (["--enable", "IC3", "--disable", "IC3IA"], {pdr_qe}, {pdr_ia}),
        (["--enable", "IC3", "--disable", "IC3QE"], {pdr_ia}, {pdr_qe}),
        (
            ["--enable", "BMC", "--enable", "IC3QE", "--enable", "IC3IA",
             "--disable", "IC3"],
            {bmc},
            {pdr_qe, pdr_ia},
        ),
        (["--enable", "IC3"], {pdr_qe, pdr_ia}, set()),
    ],
)
def test_disable_ic3(tmp_path, flags, present, absent):
    path = tmp_path / "disable_ic3.lus"
    path.write_text(model)
    used = engines(path, flags)
    assert present <= used, used
    assert not (absent & used), used
