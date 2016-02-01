#!/bin/sh

# Runs Starling and qarmc on an input file.
# Requires qarmc be on path, or the path to qarmc specified as ${QARMC}.

QARMC=${QARMC:-"qarmc"}

if [ $# != 1 ];
then
	echo "usage: $0 FILE"
	exit 1
fi

tempfile=hsf.tmp

if [ -e $tempfile ]
then
   echo "Temp file already exists: " $tempfile
   exit 1
fi

echo "--- STARLING ---"
./starling.sh -shsf $1 | tee $tempfile
echo "--- HSF ---"
$QARMC $tempfile
rm $tempfile
