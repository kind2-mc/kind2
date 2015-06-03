#!/bin/bash

# Configure 
if ./configure "$@"; then

    # Build ocamlczmq first 
    pushd ocamlczmq && ./build.sh && popd

    # Build Kind 2
    make 

fi
