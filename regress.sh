#!/bin/sh
# Runs test.sh and diffs against testresults.
# Can be used as a very basic regression test.
tempfile=testresults.tmp

if [ -e $tempfile ]
then
   echo "Temp file already exists: " $tempfile
   exit 1
fi

sort testresults | dos2unix > $tempfile
./test.sh | sort | dos2unix | diff -i -b $tempfile -
rm $tempfile