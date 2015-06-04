#!/bin/bash

# Generate aclocal.m4 from include files in m4
aclocal -I m4

# Generate configuration in ocamlczmq
pushd ocamlczmq && ./autogen.sh && popd

# Generate our configuration
autoreconf -v

