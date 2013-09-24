#!/bin/bash

# Generate configure of ZeroMQ
pushd zeromq && sh autogen.sh && popd

# Generate configure of CZMQ 
pushd czmq && sh autogen.sh && popd

# Generate our configure 
autoreconf -v

