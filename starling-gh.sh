#!/bin/sh

# Runs Starling and GRASShopper on an input file.
# Requires grasshopper.native be on path, or the path to qarmc specified as
# ${GRASSHOPPER}.

GRASSHOPPER=${GRASSHOPPER:-"grasshopper.native"}
GHARGS=${GHARGS:="-robust"}

if [ $# -lt 1 ];
then
	echo "usage: $0 FILE starling-args..."
	exit 1
fi

tempfile=grass.tmp

rm $tempfile

echo "--- STARLING ---"

if ./starling.sh -sgrass -Btry-approx $* > $tempfile;
then
	echo "Starling succeeded:"
	cat $tempfile
else
	starling_exitc=$?
	echo "Starling FAILED."
	exit $starling_exitc
fi

echo "--- GRASSHOPPER ---"

if $GRASSHOPPER ${GHARGS} $tempfile;
then
	echo "GRASShopper succeeded."
else
	gh_exitc=$?
	echo "GRASShopper FAILED."
	exit $gh_exitc
fi
