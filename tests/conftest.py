import itertools
import os
import shutil
import signal
import subprocess
from pathlib import Path
from subprocess import PIPE, CompletedProcess, Popen, TimeoutExpired

import pytest

##########
# Config #
##########

# The default arguments we want set for every run
common_args = {
    "--timeout": "84",
    "--color": "false",
    "--check_subproperties": "true",
    "--check_sat_assume": "false",
}

# How long we let a single Kind 2 run take before killing it, in seconds.
#
# Kind 2 enforces `--timeout` itself, but that enforcement has gaps: it does
# not cover parsing or the teardown of an analysis, and on Windows there is no
# SIGALRM to fall back on. This is the backstop, and it only has to be loose
# enough never to fire on a run that is making progress: without it a single
# stuck run blocks the whole session until the CI job is killed hours later.
run_timeout = float(common_args["--timeout"]) + 120

# How long we wait for the output of a run we had to kill
kill_timeout = 30

# The test conditions that are always enabled. These override common_args if
# there is a disagreement.
test_cases = {
    "slice_on": {"--slice_nodes": "on"},
}

# Additional, opt-in test conditions. Each is enabled by the command-line flag
# given below (see `pytest_addoption`).
optional_test_cases = {
    "slice_off": ("--slice-off", {"--slice_nodes": "off"}),
    "slice_experimental": ("--slice-experimental", {"--slice_nodes": "experimental"}),
}


def pytest_addoption(parser):
    parser.addoption(
        "--slice-off",
        action="store_true",
        default=False,
        help="Also run regression tests with node slicing off",
    )
    parser.addoption(
        "--slice-experimental",
        action="store_true",
        default=False,
        help="Also run regression tests with experimental node slicing",
    )


def enabled_test_cases(config):
    cases = dict(test_cases)
    for case_name, (option, case) in optional_test_cases.items():
        if config.getoption(option):
            cases[case_name] = case
    return cases

# Where to find the regression tests
regression_dir = Path("regression").absolute()

# Extra files to test with a fixed expected result, as (path, expected) pairs
extra_files = [
    (Path("../examples/syntax-test.lus").resolve(), "falsifiable"),
]

# Tests under a directory with this name pin the engine to IC3IA, so that they
# exercise IC3IA itself instead of whichever engine happens to answer first.
#
# They also pin the interpolating solver. IC3IA reaches arrays only through an
# interpolating solver that can represent them: the ones driven by quantifier
# elimination turn the engine off for such systems, so leaving the choice to
# auto-detection would make these tests vacuous wherever MathSAT is missing.
# They are skipped instead, which says so rather than reporting a run that
# never finished.
#
# These models are tiny and settle in milliseconds, so the allowance that lets
# any other test exit 30 does not apply to them: with one engine and one solver
# pinned, a 30 means IC3IA turned the system down, not that it ran out of time.
# It is therefore a failure here, which is what makes these tests notice the
# engine losing the ability to answer for such a system.
#
# The exception is the tests under `ic3ia_declined_dir_name`, which pin down
# what IC3IA must *not* say about systems it cannot reason about soundly. All
# they require is that the property is not reported falsifiable; declining to
# answer is the outcome expected today.
ic3ia_dir_name = "ic3ia"
ic3ia_declined_dir_name = "declined"
ic3ia_args = {"--enable": "IC3IA", "--smt_itp_solver": "MathSAT"}
ic3ia_solver = "mathsat"

# Where to write log files
log_dir = Path("logs")

# Where kind2 lives
kind2_exe = "kind2.exe" if os.name == "nt" else "kind2"
kind2_bin = (Path("../bin") / kind2_exe).resolve()

######################
# Test running logic #
######################

return_codes = (
    ("success", 0),
    ("falsifiable", 40),
    ("error", 3),
    ("timeout", 30),
)

expected_to_code = {expected: code for expected, code in return_codes}
code_to_expected = {code: expected for expected, code in return_codes}

# What a declined run is allowed to exit with: 30 is Kind 2's
# `incomplete_analysis`, which is what turning the system down looks like, and
# 0 covers IC3IA one day being able to answer. Every other code -- a crash, a
# usage error, a solver it could not start -- is a failure rather than a
# decline, and naming them keeps the test honest about what it pins down.
ic3ia_declined_codes = (expected_to_code["success"], expected_to_code["timeout"])

def pytest_collect_file(parent, file_path: Path):
    try:
        # We only want to collect lustre files which live under the regression dir
        relative_path = file_path.relative_to(regression_dir)
        if file_path.suffix == ".lus":
            return LustreFile.from_parent(
                parent, path=file_path, expected=str(relative_path.parents[-2])
            )
    except ValueError:
        return None


class LustreFile(pytest.File):
    def __init__(self, *, expected, **kwargs):
        super().__init__(**kwargs)
        self.expected = expected

    def collect(self):
        for case_name, case in enabled_test_cases(self.config).items():
            test_name = f"{self.path.stem} [{case_name}]"
            yield LustreItem.from_parent(
                self,
                path=self.path,
                name=test_name,
                expected=self.expected,
                case=case,
                case_name=case_name,
            )


# Make `extra_files` visible (they may be outside the `tests` directory)
def pytest_collection_modifyitems(session, items):
    extra_items = []
    for extra_path, expected in extra_files:
        collector = LustreFile.from_parent(session, path=extra_path, expected=expected)
        for item in collector.collect():
            item._nodeid = f"examples/{extra_path.name}::{item.name}"
            extra_items.append(item)
    items[:] = extra_items + items


# Tests whose run gave up before finishing, that is, exited 30 because it
# reached the `--timeout` it was given.
#
# No test expects that outcome: the regression tree only holds `success`,
# `falsifiable` and `error` cases. It is accepted anyway, since a large model
# on a slow machine may legitimately run out of time, but accepting it
# silently means a run that stops making progress passes without a trace.
# Collect them so that the session reports them at the end.
unfinished_runs = []


class LustreException(Exception): ...


class LustreTimeout(Exception):
    def __init__(self, stdout: bytes, status):
        super().__init__()
        self.stdout = stdout
        # Exit status of Kind 2 when we gave up on it, or None if it was
        # still running then
        self.status = status


def kill_tree(proc: Popen):
    """Kill `proc` and every process it spawned.

    Killing only Kind 2 can leave its solvers running, and on Windows those
    hold inherited copies of the pipes we read its output from, so reading
    them would never see the end of the output.
    """
    if os.name == "nt":
        try:
            subprocess.run(
                ["taskkill", "/F", "/T", "/PID", str(proc.pid)],
                capture_output=True,
                timeout=kill_timeout,
            )
        except (OSError, TimeoutExpired):
            pass
    else:
        # The run leads a process group of its own (see `run_kind2`), which
        # its solvers belong to as well. Address the group by the pid of its
        # leader rather than by asking for it: a group outlives its leader,
        # but `os.getpgid` does not, so looking it up would fail exactly when
        # Kind 2 has already exited and only the solvers are left to kill.
        try:
            os.killpg(proc.pid, signal.SIGKILL)
        except OSError:
            pass

    proc.kill()


def run_kind2(command) -> CompletedProcess:
    """Run Kind 2, capturing its output, and give up on it after
    `run_timeout` seconds. Raises `LustreTimeout` if we had to give up."""
    popen_args = {}
    if os.name != "nt":
        # Put the run in a process group of its own, so that the solvers it
        # spawns can be killed along with it
        popen_args["start_new_session"] = True

    proc = Popen(command, stdout=PIPE, stderr=PIPE, **popen_args)

    try:
        stdout, _ = proc.communicate(timeout=run_timeout)
    except TimeoutExpired:
        # Whether Kind 2 is still running says where the run is stuck, and
        # the two cases have nothing in common. Still running: it did not
        # honour its own `--timeout`. Already gone: the pipes are held open
        # by something it spawned and outlived it, and no timeout of its own
        # could ever have helped. Ask before killing it, which would answer
        # the question with our own signal.
        status = proc.poll()

        kill_tree(proc)
        try:
            stdout, _ = proc.communicate(timeout=kill_timeout)
        except TimeoutExpired:
            # Some process we could not kill still holds the pipes. Report
            # what we have rather than wait for the rest forever: the reader
            # threads are daemons, and they do not keep the session alive.
            stdout = b""
        raise LustreTimeout(stdout, status)

    return CompletedProcess(command, proc.returncode, stdout, None)


class LustreItem(pytest.Item):
    def __init__(self, *, expected, case, case_name, **kwargs):
        super().__init__(**kwargs)
        self.expected = expected
        self.case = case
        self.user_properties = [("case_name", case_name)]

    def _command(self):
        args = common_args | self.case

        # The error tests are expecting this flag to be set, it breaks other
        # tests
        if self.expected == "error":
            args |= {"--lus_strict": "true"}

        if self._is_ic3ia():
            args |= ic3ia_args

        arg_list = list(itertools.chain.from_iterable(args.items()))
        return [kind2_bin, *arg_list, self.path]

    def _regression_parts(self):
        # Relative to the regression tree: an absolute path would also match a
        # checkout that happens to sit under a directory of the same name, and
        # pin the whole suite to IC3IA. `extra_files` live outside the tree.
        try:
            return self.path.relative_to(regression_dir).parts
        except ValueError:
            return ()

    def _is_ic3ia(self):
        return ic3ia_dir_name in self._regression_parts()

    def _ic3ia_declines(self):
        return self._is_ic3ia() and ic3ia_declined_dir_name in self._regression_parts()

    def runtest(self):
        if self._is_ic3ia() and shutil.which(ic3ia_solver) is None:
            pytest.skip(f"{ic3ia_solver} is not installed")

        self.res = run_kind2(self._command())

        if self._ic3ia_declines():
            # Answering is allowed, answering `falsifiable` is not
            if self.res.returncode not in ic3ia_declined_codes:
                raise LustreException
            return

        # Timeout is OK, except for the IC3IA tests: see `ic3ia_dir_name`
        result = code_to_expected.get(self.res.returncode)
        if result == "timeout" and not self._is_ic3ia():
          unfinished_runs.append(self.nodeid)
          return

        if self.res.returncode != expected_to_code[self.expected]:
            raise LustreException

    def reportinfo(self) -> tuple[os.PathLike[str] | str, int | None, str]:
        return self.path, 0, self.name

    def repr_failure(self, excinfo, style=None):
        if isinstance(excinfo.value, LustreTimeout):
            status = excinfo.value.status
            if status is None:
                stuck = "Kind 2 was still running when it was killed"
            else:
                stuck = (
                    f"Kind 2 had already exited (status {status}), but its "
                    "output pipes were still open: something it spawned "
                    "outlived it"
                )
            return "\n".join(
                [
                    f"Killed after {run_timeout:.0f}s: the run did not stop "
                    f"on its own, although it was given {common_args['--timeout']}s",
                    stuck,
                    " ".join(map(str, self._command())),
                    excinfo.value.stdout.decode("utf-8"),
                ]
            )

        if isinstance(excinfo.value, LustreException):
            return_code = self.res.returncode
            actual = code_to_expected.get(
                return_code,
                f"Unknown return code: {return_code}",
            )
            return "\n".join(
                [
                    f"Expected: {self.expected}, got {actual}",
                    " ".join(map(str, self._command())),
                    self.res.stdout.decode("utf-8"),
                ]
            )

        return super().repr_failure(excinfo, style)


# Report the runs that gave up, which pass and would otherwise leave no trace
def pytest_terminal_summary(terminalreporter, exitstatus, config):
    if not unfinished_runs:
        return

    terminalreporter.section("Kind 2 ran out of time")
    terminalreporter.write_line(
        f"{len(unfinished_runs)} test(s) exited 30 after the "
        f"{common_args['--timeout']}s budget (not counted as failures):"
    )
    for nodeid in unfinished_runs:
        terminalreporter.write_line(f"  {nodeid}")


# Log test failures
def pytest_runtest_logreport(report: pytest.TestReport):
    # We only want to run this hook on failed reports
    if not (report.failed and report.when == "call"):
        return

    path, _, _ = report.location
    case_name = dict(report.user_properties).get("case_name")

    if case_name is None:
        return

    log_file: Path = log_dir / str(case_name) / f"{Path(path).name}.log"
    log_file.parent.mkdir(exist_ok=True, parents=True)

    with log_file.open("w") as f:
        f.write(report.longreprtext)
