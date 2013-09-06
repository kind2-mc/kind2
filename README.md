kind2
=====

Multi-engine SMT-based automatic model checker for safety properties of Lustre programs


Building
========

The usual

    autoconf
    ./configure 
    make

will build ZeroMQ, CZMQ, the OCaml bindings and kind2. 


ZeroMQ, CZMQ and ocamlczmq are included
=======================================

The ocamlczmq binding is included as a subtree. Nothing is needed to work with the sources, but in order to update ocamlczmq the git-subtree plugin is required. It is part of git, but not installed by default: get the git-subtree script and put it anywhere in the your path.

To update ZeroMQ and CZMQ go to the ocamlczmq repository.

To pull changes from the ocamlczmq repository do 

    git subtree pull --prefix=ocamlczmq --squash https://github.com/kind-mc/ocamlczmq.git master

For the record, initially I did 

    git subtree add --prefix=ocamlczmq --squash https://github.com/kind-mc/ocamlczmq.git master

