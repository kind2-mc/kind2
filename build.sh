#!/bin/bash

# Configure 
./configure "$@"

# Build ocamlczmq first 
pushd ocamlczmq && ./build.sh && popd

# Build Kind 2
make 

