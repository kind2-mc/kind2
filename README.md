Kind 2
======

Multi-engine SMT-based automatic model checker for safety properties of Lustre programs


Building and installing
=======================

The commands

    ./autogen.sh
    ./build.sh
    make install

will configure and build ZeroMQ, CZMQ, the OCaml bindings and Kind 2 and install the binary `kind2` into `/usr/local/bin`. Call `./build.sh --prefix=<path>` to install the Kind 2 binary into `<path>/bin` instead. If you need to pass options to the configure scripts of any of ZeroMQ, CZMQ, the OCaml bindings or Kind 2, add these to the `build.sh` call. Use `./configure --help` after `autogen.sh` to see all available options.

You need a supported SMT solver, at the momemt either CVC4 or Z3 on your path. Either one or both will be picked up by the `build.sh` command. Alternatively, you can give one or both of the options `--with-cvc4=<cvc4-executable>` and `--with-z3=<z3-executable>`. Z3 will be chosen as default if it is available, you can override this with the option `--with-default-smtsolver=cvc4`.

ZeroMQ, CZMQ and ocamlczmq are included
=======================================

The ocamlczmq binding is included as a subtree. Nothing is needed to work with the sources, but in order to update ocamlczmq the git-subtree plugin is required. It is part of git, but not installed by default: get the git-subtree script and put it anywhere in the your path.

To update ZeroMQ and CZMQ go to the ocamlczmq repository.

To pull changes from the ocamlczmq repository do 

    git subtree pull --prefix=ocamlczmq --squash https://github.com/kind-mc/ocamlczmq.git master

For the record, initially I did 

    git subtree add --prefix=ocamlczmq --squash https://github.com/kind-mc/ocamlczmq.git master

