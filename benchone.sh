#!/bin/sh

# Number of times to run ProofGen, Z3, and GRASShopper per subject
NPG=10
NZ3=10
NGH=10

name=$1
path=$2
mode=$3

TMPFILE="benchone.tmp"
rm -f $TMPFILE

COUNT=3
for i in $(seq 1 ${COUNT});
do
	./starling.sh -Pphase-time,phase-working-set,phase-virtual "${path}" >> ${TMPFILE} 2>&1
done
awk -f ./parseTimes.awk -v count="${COUNT}" ${TMPFILE}
