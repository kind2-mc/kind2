<!-- DO NOT EDIT, edit content/_index.md instead -->
[<img
src="https://github.com/kind2-mc/kind2/actions/workflows/kind2-ci.yml/badge.svg?branch=main"
class="align-middle" alt="main" />](https://github.com/kind2-mc/kind2/actions?query=workflow%3A%22Kind2+CI%22)
  [<img
src="https://img.shields.io/github/v/release/kind2-mc/kind2?color=blue"
class="align-middle" alt="release" />](https://github.com/kind2-mc/kind2/releases/latest)
 
[![License](https://img.shields.io/badge/License-Apache_2.0-blue.svg)](https://github.com/kind2-mc/kind2/blob/main/LICENSE.md)

# Kind 2


[Kind 2](http://kind.cs.uiowa.edu/) is a multi-engine, parallel,
SMT-based automatic model checker for safety properties of Lustre programs.

Kind 2 is a command-line tool.
It takes as input a Lustre file annotated with properties to be proven
invariant (see [Kind 2 Input](https://kind.cs.uiowa.edu/docs/main/user/inputs-and-outputs/lustre/)), and
outputs which of the properties are true for all inputs, as well as an input
sequence for those properties that are falsified. To ease processing by
external tools, Kind 2 can output its results in JSON and XML formats
(see [JSON / XML Output](https://kind.cs.uiowa.edu/docs/main/user/inputs-and-outputs/machine-readable-output/)).

By default Kind 2 runs a process for bounded model checking (BMC), two processes
for k-induction (one for a fixed value of k=2, and other for increasing values of k),
several processes for invariant generation, a process for IC3QE, and several processes for IC3IA
in parallel on all properties simultaneously. It incrementally outputs
counterexamples to properties as well as properties proved invariant.

The following command-line options control its operation
(run `kind2 --help` for a full list).
See [Techniques](https://kind.cs.uiowa.edu/docs/main/user/techniques/) for configuration examples and
more details on each technique.

`--enable {BMC|IND|IND2|IC3QE|IC3IA|INVGEN|INVGENOS|...}` Select model checking engines

By default, all five model checking engines are run in parallel.
Give any combination of `--enable BMC`, `--enable IND`, `--enable IND2`,
`--enable IC3QE` and `--enable IC3IA` to select which engines to run. The option `--enable BMC` alone
will not be able to prove properties valid, choosing `--enable IND` and
`--enable IND2` only (or either of the two alone) will not produce any results.
Any other combination is sound
(properties claimed to be invariant are indeed invariant) and counterexample-complete
(a counterexample will be produced for each property that is not invariant,
given enough time and resources).

`--timeout <int>` (default `0` = none) -- Run for the given number of seconds of wall clock time

`--smt_solver {Bitwuzla|cvc5|MathSAT|OpenSMT|SMTInterpol|Yices2|Z3}` (default `Z3`) -- Select SMT solver

`--bitwuzla_bin <file>` -- Executable for Bitwuzla

`--cvc5_bin <file>` -- Executable for cvc5

`--mathsat_bin <file>` -- Executable for MathSAT 5

`--opensmt_bin <file>` -- Executable for OpenSMT

`--smtinterpol_jar <file>` -- JAR of SMTInterpol

`--yices2_bin <file>` -- Executable for Yices 2 (SMT input)

`--z3_bin <file>` -- Executable for Z3

`-v` Output informational messages

`-json` Output in JSON format

`-xml` Output in XML format

## Try Kind 2 Online

Visit our [web interface](https://kind.cs.uiowa.edu/app/) to try Kind 2 from your browser.

## Download

If you use a Linux or a macOS computer, you can download an executable of the latest version
of Kind 2 from [here](https://github.com/kind2-mc/kind2/releases/latest/).
First make sure though that you have the required software described next.

## Required Software

To run Kind 2 the following software must be installed on your computer:

- Linux or macOS, and
- a supported SMT solver
  - [Bitwuzla](https://bitwuzla.github.io/) (for inputs with only machine integers),
  - [cvc5](https://cvc5.github.io/),
  - [MathSAT 5](http://mathsat.fbk.eu/index.html),
  - [OpenSMT](https://verify.inf.usi.ch/opensmt) (v2.8.0),
  - [SMTInterpol](https://ultimate.informatik.uni-freiburg.de/smtinterpol/),
  - [Yices 2](http://yices.csl.sri.com/), or
  - [Z3](https://github.com/Z3Prover/z3)

Z3 is the presently recommended SMT solver and the default option.
For best results, we recommend using a combination of several solvers.
For systems with integer and real variables, we recommend using Z3 as
the main solver (`--smt_solver Z3`) and MathSAT as
the interpolating solver (`--smt_itp_solver MathSAT`).
For systems with only machine integers, we recommend using Bitwuzla as
the main solver (`--smt_solver Bitwuzla`), MathSAT as
the interpolating solver (`--smt_itp_solver MathSAT`), and
Z3 for performing quantifier elimination (`--smt_qe_solver Z3`).

## VS Code Extension

You can also install our [extension](https://marketplace.visualstudio.com/items?itemName=kind2-mc.vscode-kind2)
for Visual Studio Code which provides support for Kind 2. The extension contains
Linux and macOS binaries for Kind 2 and Z3 ready to use. Windows is also supported
through WSL2 (see [here](https://github.com/kind2-mc/vscode-kind2#windows-advanced)
for more details).

## Docker

Kind 2 is also available on [Docker Hub](https://hub.docker.com/r/kind2/kind2/).

### Retrieving / updating the image

[Install docker](https://www.docker.com/products/docker) and then run

``` bash
docker pull kind2/kind2:dev
```

Docker will retrieve the *layers* corresponding to the latest development version of the
Kind 2 repository (`main` branch). If you are interested in the latest
release, run

``` bash
docker pull kind2/kind2
```

instead.

If you want to update your Kind 2 image to latest one, simply re-run the
`docker pull` command.

### Running Kind 2 through docker

To run Kind 2 on a file on your system, it is recommended to mount the folder
in which this file is as a [volume](https://docs.docker.com/engine/tutorials/dockervolumes/#/mount-a-host-directory-as-a-data-volume).
In practice, run

``` bash
docker run -v <absolute_path_to_folder>:/lus kind2/kind2:dev <options> /lus/<your_file>
```

where

- `<absolute_path_to_folder>` is the absolute path to the folder your file is in,
- `<your_file>` is the lustre file you want to run Kind 2 on, and
- `<options>` are some Kind 2 options of your choice.

**N.B.**

- the fact that the path to your folder must be absolute is
  [a docker constraint](https://docs.docker.com/engine/tutorials/dockervolumes/#/mount-a-host-directory-as-a-data-volume);
- mount point `/lus` is arbitrary and does not matter as long as it is
  consistent with the last argument `/lus/<your_file>`. To avoid name clashes
  with folders already present in the container however, it is recommended to
  use `/lus`;
- replace `kind2:dev` by `kind2` if you want to run the latest release of Kind2
  instead of the development version (`main` branch);
- `docker run` does **not** update your local Kind 2 image to the latest one:
  the appropriate `docker pull` command does.

### Packaging your local version of Kind 2

In the `docker` directory at the top level of the Kind 2 repository,
there is a `Dockerfile` you can use to
build your own Kind 2 image. To do so, just run

``` bash
docker build -t kind2-local -f ./docker/Dockerfile .
```

at the root of the repository. `kind2-local` is given here as an example, feel
free to call it whatever you want.

Note that building your own local Kind 2 image **does require access to the
Internet**. This is because of the packages the build process needs to
retrieve, as well as for downloading the z3 and cvc5 solvers.

## Building and installing

If you prefer, you can build Kind 2 directly from sources,
either through the OPAM package manager (recommended) or
directly using dune.

### Using OPAM

Start by installing [OPAM 2.x](https://opam.ocaml.org/)
following the instructions on the website, and
make sure OPAM has been initialized by running `opam init`.
If you want to build the development version of Kind 2
that includes the most recent changes, as opposed to
the latest release, then run

``` bash
opam pin add -n kind2 https://github.com/kind2-mc/kind2.git
```

(You can always undo this change later using this command `opam unpin kind2`).

Otherwise, skip the step above and either run

``` bash
opam install --update-invariant kind2
```

if you have OPAM 2.1 or later installed on your system, or run

``` bash
opam depext kind2
opam install --unlock-base kind2
```

if you have an older version of OPAM
(you can run `opam --version` to check the version).

This builds and installs a compatible version
of the OCaml compiler and libraries,
and the `kind2` binary.
Now you can start using `kind2`.

#### Other options using OPAM

By default, `kind2` will be installed into
the bin directory of your current OPAM switch. Run

``` bash
opam install kind2 --destdir=<DIR>
```

to install the Kind 2 binary into `<DIR>/bin`.
This will also create directories `<DIR>/doc` and `<DIR>/lib`.

In alternative, you can clone <https://github.com/kind2-mc/kind2.git>,
move to its top-level directory, and run

``` bash
make install
```

to have OPAM install `kind2` and its dependencies.

Note that z3 is available in OPAM so it is possible to install it too with OPAM by running:

``` bash
opam install z3
```

Be aware, however, that this takes quite a bit of time (up to 25 minutes).

### Direct Installation Using Dune

To build directly from sources you will also need the following software
first:

- OCaml 5.5 or later,
- [Dune 2.7 or later](https://github.com/ocaml/dune),
- dune-build-info,
- [Yojson](https://github.com/ocaml-community/yojson),
- [num](https://github.com/ocaml/num),
- [Menhir](http://gallium.inria.fr/~fpottier/menhir/) parser generator

First install this software on your system using your preferred method.
Then clone the [Kind 2 git repository](https://github.com/kind2-mc/kind2),
move to the top-level directory of the repository, and run

``` bash
dune build src @install
dune install --sections=bin --prefix <DIR>
```

to install the Kind 2 binary into `<DIR>/bin`.

You need a supported SMT solver in your PATH environment variable when running `kind2`.

## kMoXI

kMoXI (`kmoxi`) is a model checker for [MoXI](https://doi.org/10.1007/978-3-031-66149-5_2),
the Model eXchange Interlingua, a language for symbolic model checking of
transition systems built on SMT-LIB. It is a second executable built from
the Kind 2 sources: a MoXI front end on top of the engines of Kind 2
(bounded model checking, k-induction, IC3 with quantifier elimination or
with implicit abstraction, and invariant generation), which run in parallel
on the transition system of the model.

### Building

kMoXI is not distributed with the Kind 2 releases or through OPAM; build it
from a clone of this repository, with the same dependencies as Kind 2:

``` bash
make kmoxi
```

This builds and installs `bin/kmoxi`. `make test` builds it as well, and runs
its tests with those of Kind 2.

kMoXI has a version of its own, independent of that of Kind 2.
`kmoxi --version` prints it with the Kind 2 build it comes from, for
example `kMoXI v0.1.0 (Kind 2 v3.0.0-292-g700d64f)`.

### Usage

``` bash
kmoxi [options] model.moxi
```

A model declares its logic, defines one or more systems and checks the
system `main` (or any other one) with a `check-system` command that names
the conditions of its query. The answer is a MoXI `check-system-response`:
`unsat` when no execution satisfies the query, with the inductive invariant
that proves it as a certificate, or `sat`, with a witnessing trace:

``` lisp
(set-logic QF_LIA)
(define-system counter
  :input ((reset Bool))
  :output ((c Int))
  :init (= c 0)
  :trans (= c' (ite reset 0 (+ c 1))))
(check-system counter
  :input ((reset Bool))
  :output ((c Int))
  :reachable (ten (= c 10))
  :query (reach_ten (ten)))
```

```
(check-system-response
 :verbosity full
 :query (reach_ten :result sat :model reach_ten_model :trace reach_ten_trace)
 :trace (reach_ten_trace :prefix reach_ten_prefix)
 :model (reach_ten_model ())
 :trail
   (reach_ten_prefix (
                      (0 (reset false) (c 0)  (ten false) )
                      (1 (reset false) (c 1)  (ten false) )
                      ...
                      (10 (reset false) (c 10)  (ten true) )
                      )
   )
 )
```

The invariant of a certificate, `:certificate (q_cert :inv I :k k)`, is a
term over the variables of the check, which the MoXI definition leaves the
format of open. It is an SMT-LIB term, except that a variable of a
subsystem instance is named by a qualified name: the path of the instances
down to it, each name quoted on its own if needed and joined by `::`
without spaces, as `C1::l` or `C1::|the sub|::l`. No SMT-LIB token contains
`::` outside quotes, so the path is told apart from a variable `|C1::l|` of
the check, and from a variable `|C::l|` of the instance `C1`. A variable of
kMoXI's own encoding is named after an `@`, which SMT-LIB reserves for
solvers: the one a reachability condition `r` is encoded by, `@r`, holds in
the initial state and in each state whose predecessor does not satisfy `r`;
in a query with several reachability conditions, `@held::r` is whether `r`
has held so far.
A trail names the variables it shows the same way, and shows a reachability
condition under the name `r` the check declares it with, which no variable
of the check may have, rather than as `@r`. The trail of a query with
several reachability conditions shows none of them; it ends where the last
one holds.

A `check-system` command may have several queries, which kMoXI answers in
the order of the command. The queries with the same `:assumption`
conditions and `:current` condition are properties of one system, which
the engines analyze together. A `:current` condition replaces the initial
condition (`:init`) of the checked system and of the systems it calls, but
not their invariants (`:inv`).

The exit code is 0 when the analysis completes, whatever the answer; it is
3 when the model does not parse or type check, and `--only_parse true`
stops after that check. Useful options, all shared with Kind 2:

- `--timeout <seconds>`: wall-clock timeout of the analysis;
- `--enable <engine>`: run only the given engines, for example
  `--enable BMC --enable IND`;
- `--smt_solver`, `--smt_itp_solver`, `--smt_qe_solver`: the main,
  interpolating and quantifier-elimination solvers, with `--z3_bin`,
  `--bitwuzla_bin`, `--mathsat_bin` and the like to locate them. Without
  these, kMoXI picks them among the solvers it finds on the path as `kind2`
  does, except that it prefers Bitwuzla as the main solver when the model
  sets the logic `QF_BV`.

`kmoxi --help` lists the options, and `kmoxi --help_of all` those of the
engines.

### Supported subset of MoXI

kMoXI reads native MoXI (the S-expression syntax) with the logics `QF_BV`,
`QF_ABV`, `QF_LIA`, `QF_LRA` and `QF_NIA`, and checks every model against
the MoXI language definition before analyzing it. Its restrictions:

- `:fairness` conditions (liveness queries) are not supported;
- a `:queries` attribute with several queries is not supported in a model
  with declared constants (`declare-const`), since its queries must agree
  on the values of the constants; without them, its queries are answered
  as separate queries;
- arrays are indexed by bit-vectors, and their elements are not of an
  enumeration sort;
- the values of an enumeration sort (`declare-enum-sort`) stand for
  integers, so a model with one needs a solver with integer arithmetic,
  such as Z3, even in `QF_BV`;
- uninterpreted sorts and functions (`declare-sort`, `declare-fun`) are not
  supported; constants (`declare-const`) are.

## Development

With OPAM 2.x you can create a local switch which will install all dependencies automatically.

``` bash
opam switch create .
make
```

Alternatively, you can install all dependencies in your current switch by running:

``` bash
opam install . --deps-only
make
```

For running the unit tests for front end, you can install ounit2 library using opam by running:

``` bash
opam install ounit2
```

To run the ounit tests, you can use the following dune command:

``` bash
dune test
```

To run regression tests, you need a Python interpreter and
the [pytest](https://pypi.org/project/pytest/) module. The simplest way to do
this is to install [uv](https://docs.astral.sh/uv/). The test-running script
will try to use `uv` to set up its own isolated python environment with `pytest`,
so the rest of your system will not be impacted. If it fails to find `uv`, it will
fallback to trying to use `pytest` in your system's Python interpreter.

``` bash
make test
```

## Documentation

Documentation is available online in [HTML](http://kind.cs.uiowa.edu/kind2_user_doc/)
or [PDF](http://kind.cs.uiowa.edu/kind2_user_doc/doc.pdf) forms.

See `doc/content/README.md` for more information.
