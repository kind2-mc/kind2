"""BMC reports a falsified property as soon as it finds its counterexample.

At each bound, BMC asks the solver for a counterexample to the properties it
has not settled yet, removes those it falsifies, and asks again for the rest.
It used to report the falsified properties only once no counterexample was
left at that bound. If a later query never returns, the counterexample it had
already found was never reported. Here, f is defined at the SMT level, and
the query for "nonneg" needs induction over its definition, which the solver
does not do: it keeps unfolding f. "not_three" is falsified at bound 0 by an
earlier query, and must be reported although "nonneg" never is.

The model is not in the regression tree: with every engine enabled, the run
would only stop at the timeout, since "nonneg" is never settled.
"""

import json
import subprocess

from conftest import common_args, kind2_bin, run_timeout

model = """
function rec f (n: int) returns (r: int);
con
  decreases n;
noc
let
  r = when n <= 0 then 0 else f(n - 2);
tel

node main (x: int) returns (y: int);
let
  y = f(x);
  check "nonneg" y >= 0;
  check "not_three" x <> 3;
tel
"""


def test_falsified_property_reported_while_query_runs(tmp_path):
    path = tmp_path / "bmc_reports_early.lus"
    path.write_text(model)
    args = common_args | {"--timeout": "10"}
    arg_list = [arg for pair in args.items() for arg in pair]
    run = subprocess.run(
        [kind2_bin, "-json", *arg_list, "--enable", "BMC", str(path)],
        capture_output=True,
        text=True,
        timeout=run_timeout,
    )
    answers = {
        obj["name"]: obj["answer"]["value"]
        for obj in json.loads(run.stdout)
        if obj.get("objectType") == "property"
    }
    assert answers.get("not_three") == "falsifiable", answers
