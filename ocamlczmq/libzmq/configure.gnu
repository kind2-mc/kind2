#!/bin/bash

# Pass options to configure and override prefix
./configure $* --with-libsodium=no --prefix=$PWD/..

