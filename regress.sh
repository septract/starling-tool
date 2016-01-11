#!/bin/sh
# Runs test.sh and diffs against testresults.
# Can be used as a very basic regression test.
./test.sh | dos2unix | sort | diff -i -b testresults -
