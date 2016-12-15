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
./starling.sh -sgrass -Btry-approx $* | tee $tempfile
echo "--- GRASSHOPPER ---"
$GRASSHOPPER -robust $tempfile && echo "success"
rm $tempfile
