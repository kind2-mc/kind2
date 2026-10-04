"""IC3 is a virtual module that stands for both IC3QE and IC3IA.

Enabling IC3 enabled both engines, but disabling IC3 disabled neither: the
disabled modules were removed from the enabled ones as given, and IC3 is
never one of the enabled modules by default. A run with --disable IC3 still
ran both engines. Likewise, --enable IC3 --disable IC3IA still ran IC3IA.

The same held for the check that disables IC3 with a version of Yices 2
older than 2.6: it looked for IC3 among the enabled modules, which only hold
IC3QE and IC3IA, so it never fired.

The engines a run uses are listed in its verbose output. The property is
falsified at once by every engine, so that each run stops right away.
"""

import shutil
import subprocess
import sys

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


def run_verbose(path, flags):
    args = common_args | {"--timeout": "20"}
    arg_list = [arg for pair in args.items() for arg in pair]
    run = subprocess.run(
        [kind2_bin, "-v", *arg_list, *flags, str(path)],
        capture_output=True,
        text=True,
        timeout=run_timeout,
    )
    return run.stdout


def engines_of_output(output):
    lines = output.splitlines()
    start = next(
        i for i, line in enumerate(lines) if "Running in parallel mode:" in line
    )
    names = []
    for line in lines[start:]:
        if "- " not in line:
            break
        names.append(line.split("- ", 1)[1].strip())
    return set(names)


def engines(path, flags):
    return engines_of_output(run_verbose(path, flags))


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


yices = shutil.which("yices-smt2")


@pytest.mark.skipif(
    yices is None or sys.platform == "win32",
    reason="needs yices-smt2 and a POSIX shell to stand in for an old version",
)
@pytest.mark.parametrize(
    "flags",
    [[], ["--enable", "IC3"], ["--enable", "IC3IA"]],
)
def test_old_yices_disables_ic3(tmp_path, flags):
    path = tmp_path / "disable_ic3.lus"
    path.write_text(model)
    # Report version 2.5.4, and let the real Yices answer everything else
    old_yices = tmp_path / "yices-smt2"
    old_yices.write_text(
        "#!/bin/sh\n"
        'if [ "$1" = "--version" ]; then echo "Yices 2.5.4"; exit 0; fi\n'
        f'exec "{yices}" "$@"\n'
    )
    old_yices.chmod(0o755)
    output = run_verbose(
        path,
        ["--smt_solver", "Yices2", "--yices2_bin", str(old_yices), *flags],
    )
    assert "disabling IC3" in output, output
    if "Running in parallel mode:" in output:
        assert not ({pdr_qe, pdr_ia} & engines_of_output(output)), output
