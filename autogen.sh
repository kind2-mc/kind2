#!/bin/bash

# Generate configuration in ocamlczmq
pushd ocamlczmq && ./autogen.sh && popd

# Generate our configuration
autoreconf -v

