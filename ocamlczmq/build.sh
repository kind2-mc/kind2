#!/bin/bash
set -e

# Configure with ZeroMQ and without CZMQ first 
./configure "$@" --with-zmq

# Build ZeroMQ
make zmq

# Configure with CZMQ and without ZeroMQ (already configured)  
./configure "$@" --with-czmq

# Build ZeroMQ
make czmq

# Build ocamlczmq
make

