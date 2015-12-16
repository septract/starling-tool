#!/bin/sh
# Runs test.sh and diffs against testresults.
# Can be used as a very basic regression test.

./test.sh | diff testresults -
