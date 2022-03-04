#!/bin/sh
# Run command passed as argument and print stderr output
# only if the command failed to execute
tempfile=$(mktemp)
$@ 2> $tempfile
status=$?
if [ $status -ne 0 ]; then
  cat $tempfile 1>&2
fi
rm $tempfile
exit $status