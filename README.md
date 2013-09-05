ocamlczmq
=========

Ocaml binding to the high-level C binding for ØMQ

Building
========

The usual

    autoconf
    ./configure --with-libzmq=<path to lib/libzmq.so>
    make

will build both CZMQ and the OCaml bindings. 

CZMQ is included
================

The CZMQ high-level C binding for ØMQ is included as a subtree. Nothing is needed to work with the sources, but in order to update CZMQ the git-subtree plugin is required. It is part of git, but not installed by default: get the git-subtree script and put it anywhere in the your path.

To pull changes from the CZMQ repository do 

   git subtree pull --prefix=czmq --squash https://github.com/zeromq/czmq.git master

For the record, initially I did 

    git subtree add --prefix=czmq --squash https://github.com/zeromq/czmq.git master

