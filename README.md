kind2
=====

Multi-engine SMT-based automatic model checker for safety properties of Lustre programs


Building
========

The OCaml binding to ØMQ is included as a submodule, which in turn inclides the CZMQ high-level C binding for ØMQ as a submodule, hence you need to do a 

    git submodule init
    git submodule update

to also clone the ocamlczmq repository. Then do 

    cd ocamlczmq
    git submodule init
    git submodule update

to clone the CZMQ repository.

Then the usual

    autoconf
    ./configure --with-libzmq=<path to lib/libzmq.so>
    make

will build both CZMQ and the OCaml bindings. 