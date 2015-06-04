#!/bin/bash

# Generate aclocal.m4 from include files in m4
aclocal -I m4

# Generate configure of ZeroMQ
pushd zeromq && sh autogen.sh && popd

# Generate configure of CZMQ 
pushd czmq && sh autogen.sh && popd

# Generate our configure 
autoreconf -vfi

