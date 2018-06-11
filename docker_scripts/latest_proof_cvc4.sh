#!/bin/bash

url="http://cvc4.cs.stanford.edu/downloads/builds/x86_64-linux-opt/unstable/"

latest=`wget -qO - $url | grep -P -o "cvc4-.*?-opt" | tail -1`

if [ -n "$latest" ]
then
  echo "latest cvc4 version is $latest"
  wget -O cvc4 "$url$latest"
  exit $?
else
  echo "could not retrieve latest cvc4 version"
  exit 2
fi
