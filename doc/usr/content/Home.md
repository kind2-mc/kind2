# Kind 2

A multi-engine, parallel, SMT-based automatic model checker for safety properties of Lustre programs. [License information](./9_other/license.md#apache-license).

Kind 2 takes as input a Lustre file annotated with properties to prove
invariant (see [Lustre syntax](./1_input/1_lustre.md#lustre)), and outputs
which of the properties are true for all inputs, as well as an input sequence
for those properties that are falsified. To ease processing by front-end tools,
Kind 2 can output its results in [XML format](./2_output/2_xml.md#xml).
Input can also be given in the [native format](./1_input/2_native.md#native-format).

Kind 2 runs a process for bounded model checking (BMC), a process for k-induction, and a process for IC3 in parallel on all properties simultaneously. It incrementally outputs counterexamples to properties as well as properties proved invariant.

The following command-line options control its operation (run ```kind2 --help``` for a full list).

```--enable {BMC|IND|PDR}``` Select model checking engines
   
By default, all three model checking engines are run in parallel. Give any combination of ```--enable BMC```, ```--enable IND``` and ```--enable PDR``` to select which engines to run. The option ``--enable BMC`` alone will not be able to prove properties valid, choosing ``--enable IND`` only will not produce any results. Any other combination is sound (properties claimed to be invariant are indeed invariant) and counterexample-complete (a counterexample will be produced for each property that is not invariant, given enough time and resources).

```--timeout_wall SECS``` Run for SECS seconds of wall clock time

```--timeout_virtual SECS``` Run for SECS of CPU time
 
```--smtsolver {Z3|CVC4|mathsat5} ``` Select SMT solver

The default is ```Z3```, but see options of the ```./build.sh``` script to override at compile time
  
```--z3_bin PROGRAM``` Executable for Z3

```--cvc4_bin PROGRAM``` Executable for CVC4

```--mathsat5_bin PROGRAM``` Executable for MathSat5

```--bmc_max K``` Run bounded model checking for up to ```K``` steps

```-v``` Output informational messages

```-xml``` Output in XML format


## Requirements

- Linux or Mac OS X,
- OCaml 4.02 or later,
- Camlp4 
- [Menhir](http://gallium.inria.fr/~fpottier/menhir/) parser generator, and
- a supported SMT solver
    - [Z3](http://z3.codeplex.com) (presently recommended), 
    - [CVC4](http://cvc4.cs.nyu.edu), (must use ```--pdr_tighten_to_unsat_core false```) or
    - [MathSat5](http://mathsat.fbk.eu/)

## Building and installing

If you got the sources from the Github repository, you need to run first

    ./autogen.sh

By default, `kind2` will be installed into `/usr/local/bin`, an operation for which you usually need to be root. Call 

    ./build.sh --prefix=PATH
    
to install the Kind 2 binary into `PATH/bin`. You can omit the option to accept the default path of `/usr/local/bin`. 

The ZeroMQ and CZMQ libraries, and OCaml bindings to CZMQ are distributed with Kind 2. The build script will compile and link to those, ignoring any versions that are installed on your system. 

If it has been successful, call 

    make install

to install the Kind 2 binary into the chosen location. If you need to pass options to the configure scripts of any of ZeroMQ, CZMQ, the OCaml bindings or Kind 2, add these to the `build.sh` call. Use `./configure --help` after `autogen.sh` to see all available options.

You need a supported SMT solver, at the momemt either Z3, CVC4 or MathSat5 on your path when running `kind2`. 
