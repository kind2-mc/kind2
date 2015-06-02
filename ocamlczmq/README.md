ocamlczmq
=========

Ocaml binding to the high-level C binding for ØMQ

Building
========

The commands

    ./autogen.sh
    ./build.sh

will configure and build ZeroMQ, CZMQ and the OCaml binding. If you need to pass options to the configure script of any of ZeroMQ, CZMQ or ocamlczmq, add those to the `build.sh` call.

CZMQ and ZeroMQ are included
================

ZeroMQ and the CZMQ high-level C binding for ØMQ are included as subtrees from their respective github repositories. Nothing is needed to work with the sources, but in order to update ZeroMQ and CZMQ the git-subtree plugin is required. It is part of git, but not installed by default: get the git-subtree script and put it anywhere in the your path.

To pull a new release from the repositories do (adjust the tag to the new release)

    git subtree pull --prefix=zeromq --squash https://github.com/zeromq/zeromq3-x tags/v3.2.5
    git subtree pull --prefix=czmq --squash https://github.com/zeromq/czmq tags/v2.2.0

For the record, initially I did 

    git subtree add --prefix=zeromq --squash https://github.com/zeromq/zeromq3-x tags/v3.2.3
    git subtree add --prefix=czmq --squash https://github.com/zeromq/czmq tags/v1.4.1

