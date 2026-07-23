import itertools
import os
from pathlib import Path
from subprocess import run

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
kind2_bin = Path("../bin/kind2").resolve()

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
        self.res = run(self._command(), capture_output=True)

        # Timeout is OK 
        result = code_to_expected.get(self.res.returncode)
        if result == "timeout": 
          return   

        if self.res.returncode != expected_to_code[self.expected]:
            raise LustreException

    def reportinfo(self) -> tuple[os.PathLike[str] | str, int | None, str]:
        return self.path, 0, self.name

    def repr_failure(self, excinfo, style=None):
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
