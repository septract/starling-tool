#!/bin/sh

# Number of times to run ProofGen, Z3, and HSF per subject
NPG=1
NZ3=1
NHSF=1

name=$1
path=$2
z3=$3
hsf=$4
oz3=$5
ohsf=$6

# Flag for removing optimisations
NOPTS="-Ono-all"

# Stage for proofgen
PGSTAGE="-ssymproof"

terms=$(./starling.sh ${NOPTS} "$path" | wc -l)
>&2 echo "non-optimised terms: ${terms}"

oterms=$(./starling.sh "$path" | wc -l)
>&2 echo "optimised terms: ${oterms}"

OPTS=""

#
# Proofgen
#

>&2 echo "Proofgen: no optimisations"
pgtotal="0"
	
for i in $(seq 1 "${NPG}");
do
	time=$(/usr/bin/time ./starling.sh ${NOPTS} ${PGSTAGE} "$path" 2>&1 >/dev/null | awk '/real/ { print $3 }')
	pgtotal=$(dc -e "2 k ${pgtotal} ${time} + p")

	>&2 echo "- run ${i}: ${time}s, total so far ${pgtotal}"
done
pgfinal=$(dc -e "2 k $pgtotal $NPG / p")
>&2 echo "Proofgen: no optimisations RESULT: ${pgfinal}s"

>&2 echo "Proofgen: optimisations"
opgtotal="0"
	
for i in $(seq 1 "${NPG}");
do
	time=$(/usr/bin/time ./starling.sh ${PGSTAGE} "$path" 2>&1 >/dev/null | awk '/real/ { print $3 }')
	opgtotal=$(dc -e "2 k ${opgtotal} ${time} + p")

	>&2 echo "- run ${i}: ${time}s, total so far ${opgtotal}"
done
opgfinal=$(dc -e "2 k $opgtotal $NPG / p")
>&2 echo "Proofgen: no optimisations RESULT: ${opgfinal}s"


#
# Z3
#

if [ "$z3" = "yes" ];
then 
	>&2 echo "Z3: no optimisations"

	z3total="0"
	
	for i in $(seq 1 "${NZ3}");
	do
		time=$(/usr/bin/time ./starling.sh ${NOPTS} "$path" 2>&1 >/dev/null | awk '/real/ { print $3 }')
		z3total=$(dc -e "2 k ${z3total} ${time} + p")

		>&2 echo "- run ${i}: ${time}s, total so far ${z3total}"
	done
	z3final=$(dc -e "2 k $z3total $NZ3 / p")
	>&2 echo "Z3: no optimisations RESULT: ${z3final}s"
else
	>&2 echo "Z3: no optimisations SKIPPED"

	z3final="--"
fi

if [ "$oz3" = "yes" ];
then 
	>&2 echo "Z3: optimisations"

	oz3total="0"
	
	for i in $(seq 1 "${NZ3}");
	do
		time=$(/usr/bin/time ./starling.sh "$path" 2>&1 >/dev/null | awk '/real/ { print $3 }')
		oz3total=$(dc -e "2 k ${oz3total} ${time} + p")

		>&2 echo "- run ${i}: ${time}s, total so far ${oz3total}"
	done
	oz3final=$(dc -e "2 k $oz3total $NZ3 / p")
	>&2 echo "Z3: optimisations RESULT: ${oz3final}s"
else
	>&2 echo "Z3: optimisations SKIPPED"

	oz3final="--"
fi


#
# HSF
#

if [ "$hsf" = "yes" ];
then 
	>&2 echo "HSF: no optimisations"

	hsftotal="0"
	
	for i in $(seq 1 "${NHSF}");
	do
		rm -f hsf.tmp
		time=$(/usr/bin/time ./starling-hsf.sh "$path" ${NOPTS} 2>&1 >/dev/null | awk '/real/ { print $3 }')
		hsftotal=$(dc -e "2 k ${hsftotal} ${time} + p")

		>&2 echo "- run ${i}: ${time}s, total so far ${hsftotal}"
	done
	hsffinal=$(dc -e "2 k $hsftotal $NHSF / p")
	>&2 echo "HSF: no optimisations RESULT: ${hsffinal}s"
else
	>&2 echo "HSF: no optimisations SKIPPED"

	hsffinal="--"
fi

if [ "$ohsf" = "yes" ];
then 
	>&2 echo "HSF: optimisations"

	ohsftotal="0"
	
	for i in $(seq 1 "${NHSF}");
	do
		rm -f hsf.tmp
		time=$(/usr/bin/time ./starling-hsf.sh "$path" 2>&1 >/dev/null | awk '/real/ { print $3 }')
		ohsftotal=$(dc -e "2 k ${ohsftotal} ${time} + p")

		>&2 echo "- run ${i}: ${time}s, total so far ${ohsftotal}"
	done
	ohsffinal=$(dc -e "2 k $ohsftotal $NHSF / p")
	>&2 echo "HSF: optimisations RESULT: ${ohsffinal}s"
else
	>&2 echo "HSF: optimisations SKIPPED"

	ohsffinal="--"
fi

echo "--${name}&${terms}&${pgfinal}&${z3final}&${hsffinal}&${oterms}&${opgfinal}&${oz3final}&${ohsffinal}\\\\"
