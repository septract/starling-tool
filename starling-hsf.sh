#!/bin/sh

# Runs Starling and qarmc on an input file.
# Requires qarmc be on path, or the path to qarmc specified as ${QARMC}.

QARMC=${QARMC:-"qarmc"}

if [ $# -lt 1 ];
then
	echo "usage: $0 FILE starling-args..."
	exit 1
fi

tempfile=hsf.tmp

if [ -e $tempfile ]
then
   echo "Temp file already exists: " $tempfile
   exit 1
fi

echo "--- STARLING ---"
# no-smt-reduce is needed to give HSF enough contraints to be practical.
if ./starling.sh -shsf -Bno-smt-reduce $* > $tempfile;
then
	echo "Starling succeeded:"
	cat $tempfile
else
	starling_exitc=$?
	echo "Starling FAILED."
    rm $tempfile
	exit $starling_exitc
fi

echo "--- HSF ---"
$QARMC -get-model $tempfile
rm $tempfile
