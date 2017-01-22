#!/bin/sh

# Number of times to run ProofGen, Z3, and GRASShopper per subject
NPG=10
NZ3=10
NGH=10

name=$1
path=$2
mode=$3

TMPZ3="benchone.z3.tmp"
TMPAWK="benchone.awk.tmp"
TMPSPL="benchone.spl.tmp"
TMPGH="benchone.z3.gh"
rm -f $TMPZ3 $TMPAWK $TMPSPL $TMPGH

#
# Zeroth pass: dump proof LoC into awk file
#

loc=$(wc -l "${path}" | sed 's/^ *\([0-9]\{1,\}\).*/\1/')
printf "LOC:Starling %d\n" "${loc}" > ${TMPAWK}

#
# First pass: get SMT results and format them
#

COUNT=3
for i in $(seq 1 ${COUNT});
do
	./starling.sh -Pphase-time,phase-working-set,phase-virtual "${path}" >> ${TMPZ3} 2>&1
done
awk -f ./parseZ3.awk -v count="${COUNT}" ${TMPZ3} >> ${TMPAWK}

#
# Second pass: call GRASShopper if needed
#

if [ "${mode}" = "gh" ];
then
	./starling.sh -sgrass "${path}" > "${TMPSPL}"

	# Get lines of GRASShopper code.
	gloc=$(wc -l "${TMPSPL}" | sed 's/^ *\([0-9]\{1,\}\).*/\1/')
	printf "LOC:GH %d\n" "${gloc}" >> ${TMPAWK}

	# Time GRASShopper.
	gatime=0
	for i in $(seq 1 ${COUNT});
	do
		gntime=$(/usr/bin/time -p ${GRASSHOPPER} ${TMPSPL} 2>&1 | grep "real" | sed 's/[a-zA-Z ]\{1,\}//')
		gatime=$(dc -e "2 k ${gatime} ${gntime} + p")
	done
	gtime=$(dc -e "2 k $gatime $COUNT / p")
	printf "Elapsed:GH %.2f\n" "${gtime}" >> ${TMPAWK}
fi

awk -f benchToLatex.awk -v mode="${mode}" "${TMPAWK}"
