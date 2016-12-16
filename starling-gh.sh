#!/bin/sh

# Runs Starling and GRASShopper on an input file.
# Requires grasshopper.native be on path, or the path to qarmc specified as
# ${GRASSHOPPER}.

GRASSHOPPER=${GRASSHOPPER:-"grasshopper.native"}

if [ $# -lt 1 ];
then
	echo "usage: $0 FILE starling-args..."
	exit 1
fi

tempfile=grass.tmp

if [ -e $tempfile ]
then
   echo "Temp file already exists: " $tempfile
   exit 1
fi

echo "--- STARLING ---"

if ./starling.sh -sgrass -Btry-approx $* > $tempfile;
then
	echo "Starling succeeded:"
	cat $tempfile
else
	starling_exitc=$?
	echo "Starling FAILED."
	rm $tempfile
	exit $starling_exitc
fi

echo "--- GRASSHOPPER ---"

if $GRASSHOPPER -robust $tempfile;
then
	echo "GRASShopper succeeded."
else
	gh_exitc=$?
	echo "GRASShopper FAILED."
	rm $tempfile
	exit $gh_exitc
fi

rm $tempfile
