#!/bin/sh

NZ3=1
NHSF=1

name=$1
path=$2
z3=$3
hsf=$4
oz3=$5
ohsf=$6

terms=$(./starling.sh -Ono-all "$path" | wc -l)
>&2 echo "non-optimised terms: ${terms}"

oterms=$(./starling.sh "$path" | wc -l)
>&2 echo "optimised terms: ${oterms}"

if [ "$z3" = "yes" ];
then 
	>&2 echo "Z3: no optimisations"

	z3total="0"
	
	for i in $(seq 1 "${NZ3}");
	do
		time=$(/usr/bin/time ./starling.sh -Ono-all "$path" 2>&1 >/dev/null | awk '/real/ { print $3 }')
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

if [ "$hsf" = "yes" ];
then 
	>&2 echo "HSF: no optimisations"

	hsftotal="0"
	
	for i in $(seq 1 "${NHSF}");
	do
		rm -f hsf.tmp
		time=$(/usr/bin/time ./starling-hsf.sh "$path" -Ono-all 2>&1 >/dev/null | awk '/real/ { print $3 }')
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

echo "--${name}&${terms}&${z3final}&${hsffinal}&${oterms}&${oz3final}&${ohsffinal}\\"
