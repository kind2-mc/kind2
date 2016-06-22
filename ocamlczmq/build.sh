#!/bin/bash
set -e

# get number of processors for parallel compilation
NBPROCS=`getconf _NPROCESSORS_ONLN`

# Configure with ZeroMQ and without CZMQ first 
./configure "$@" --with-zmq

# Build ZeroMQ
make -j$NBPROCS zmq

# Configure with CZMQ and without ZeroMQ (already configured)  
./configure "$@" --with-czmq

# Build ZeroMQ
make -j$NBPROCS czmq

# Build ocamlczmq
make -j$NBPROCS

