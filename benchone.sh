#!/bin/sh

# Number of times to run ProofGen, Z3, and GRASShopper per subject
NPG=10
NZ3=10
NGH=10

name=$1
path=$2
mode=$3

echo $1 $2 $3

TMPFILE="benchone.tmp"
rm -f $TMPFILE

COUNT=10
for i in $(seq 1 ${COUNT});
do
	./starling.sh --times "${path}" >> ${TMPFILE}
done
awk -f ./parseTimes.awk -v count="${COUNT}" ${TMPFILE}
