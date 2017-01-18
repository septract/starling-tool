#!/bin/sh
#
# Runs `benchone.sh` on each example specified in `benchmarks.in`.
# See those files for more information.
#

IFS=:
cat=""
sed -e 's/#.*$//' -e '/^$/d' ./benchmarks.in | while read mode name path; do
	# Print backend header if we're on a new backend.
	if [ "${mode}" != "${cat}" ];
	then
		if [ "${mode}" = "gh" ];
		then
			fmode="GRASShopper"
		elif [ "${mode}" = "z3" ];
		then
			fmode="Z3"
		else
			fmode="??"
		fi

		echo "\\midrule"
		echo "${fmode}&&&&&&&&"'\\\\'
		cat="$mode"
	fi

	>&2 echo "--- ${name} : ${path} (${mode}) ---"

	./benchone.sh "${name}" "${path}" "${mode}"
done
