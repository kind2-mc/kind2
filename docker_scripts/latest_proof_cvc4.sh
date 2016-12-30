#!/bin/bash

index_file="index"
tmp_file="tmp_index"

wget -O $index_file http://cvc4.cs.nyu.edu/cvc4-builds/x86_64-linux-opt-proofs/unstable/

cat $index_file \
| grep linux-opt-proofs \
| sed -e 's:.*\(cvc4-20.*\)".*:\1:'> $tmp_file

latest=""

while read line
do
  latest="$line"
done < $tmp_file

rm $index_file $tmp_file

if [ -n "$latest" ]
then
  echo "latest cvc4 version is $latest"
  wget -O cvc4 "http://cvc4.cs.nyu.edu/cvc4-builds/x86_64-linux-opt-proofs/unstable/$latest"
else
  echo "could not retrieve latest cvc4 version"
  exit 2
fi