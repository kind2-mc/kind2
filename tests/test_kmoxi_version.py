"""kmoxi has a version of its own, independent of that of Kind 2.

`kmoxi --version` used to print the version of Kind 2, as `kind2 --version`
does. It now prints the version of kmoxi, with the Kind 2 build it comes
from; kind2 is unchanged.
"""

import re

import pytest

from conftest import kind2_bin, kmoxi_bin, run_kind2


def version(binary):
    if not binary.exists():
        pytest.skip(f"{binary} is not built")
    res = run_kind2([binary, "--version"])
    assert res.returncode == 0, res.stdout + res.stderr
    return res.stdout.decode().strip()


def test_kmoxi_version():
    kind2 = version(kind2_bin)
    assert re.fullmatch(r"kind2 v\S+", kind2), kind2
    kmoxi = version(kmoxi_bin)
    # The Kind 2 build is that of kind2, built from the same sources
    build = re.escape(kind2.split(" ", 1)[1])
    assert re.fullmatch(rf"kMoXI v\d+\.\d+\.\d+ \(Kind 2 {build}\)", kmoxi), kmoxi
