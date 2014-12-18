#!/bin/bash

# Configure with ZeroMQ and without CZMQ first 
./configure "$@" --with-zeromq

# Build ZeroMQ
make zeromq

# Configure with CZMQ and without ZeroMQ (already configured)  
./configure "$@" --with-czmq

# Build ZeroMQ
make czmq

# Build ocamlczmq
make 

