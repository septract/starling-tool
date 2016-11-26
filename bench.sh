#!/bin/sh
#
# Runs `benchone.sh` on each example specified in `benchmarks.in`.
# See those files for more information.
#

IFS=:
cat=""
sed -e 's/#.*$//' -e '/^$/d' ./benchmarks.in | while read category name path z3 hsf oz3 ohsf; do
	# Print category header if we're on a new category.
	if [ "${category}" != "${cat}" ];
	then
		echo "\\midrule"
		echo "${category}&&&&&&&&"'\\\\'
		cat="$category"
	fi

	>&2 echo "--- ${category} : ${name} (${path}) ---"

	./benchone.sh "${name}" "${path}" "${z3}" "${hsf}" "${oz3}" "${ohsf}"
done
