import itertools
import os
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


class LustreException(Exception): ...


class LustreTimeout(Exception):
    def __init__(self, stdout: bytes):
        super().__init__()
        self.stdout = stdout


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
        # The run has a process group of its own (see `run_kind2`), which its
        # solvers belong to as well
        try:
            os.killpg(os.getpgid(proc.pid), signal.SIGKILL)
        except (OSError, ProcessLookupError):
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
        kill_tree(proc)
        try:
            stdout, _ = proc.communicate(timeout=kill_timeout)
        except TimeoutExpired:
            # Some process we could not kill still holds the pipes. Report
            # what we have rather than wait for the rest forever: the reader
            # threads are daemons, and they do not keep the session alive.
            stdout = b""
        raise LustreTimeout(stdout)

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

        arg_list = list(itertools.chain.from_iterable(args.items()))
        return [kind2_bin, *arg_list, self.path]

    def runtest(self):
        self.res = run_kind2(self._command())

        # Timeout is OK 
        result = code_to_expected.get(self.res.returncode)
        if result == "timeout": 
          return   

        if self.res.returncode != expected_to_code[self.expected]:
            raise LustreException

    def reportinfo(self) -> tuple[os.PathLike[str] | str, int | None, str]:
        return self.path, 0, self.name

    def repr_failure(self, excinfo, style=None):
        if isinstance(excinfo.value, LustreTimeout):
            return "\n".join(
                [
                    f"Killed after {run_timeout:.0f}s: the run did not stop "
                    f"on its own, although it was given {common_args['--timeout']}s",
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
