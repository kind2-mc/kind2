#!/bin/bash

export libzmq_CFLAGS="-I`pwd`/../include"
export libzmq_LIBS="-L`pwd`/../lib"
export CFLAGS="-I`pwd`/../include"
export LDFLAGS="-L`pwd`/../lib -lzmq"
export LD_LIBRARY_PATH="`pwd`/../lib"

# Pass options to configure and override prefix
./configure --prefix=$PWD/.. --with-libzmq=$PWD/..

