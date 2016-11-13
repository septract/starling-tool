#!/bin/sh
#
# Runs Starling in Z3 mode on each passing and failing example N times, and
# reports the results.
#
# The results are in the form 'FILENAME RUN TIME', and can be awked into a
# proper benchmark set.

IFS=:
cat=""
sed -e 's/#.*$//' -e '/^$/d' ./benchmarks.in | while read category name path z3 hsf oz3 ohsf; do
	# Print category header if we're on a new category.
	if [ "${category}" != "${cat}" ];
	then
		echo "${category}&&&&&&"
		cat="$category"
	fi

	>&2 echo "--- ${category} : ${name} (${path}) ---"

	./benchone.sh "${name}" "${path}" "${z3}" "${hsf}" "${oz3}" "${ohsf}"
done
