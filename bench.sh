#!/bin/sh
#
# Runs `benchone.sh` on each example specified in `benchmarks.in`.
# See those files for more information.
#

IFS=:

if [ "$1" == "no-approx" ];
then
	approx=""
	opt="-Ono-all"
else
	approx="-Btry-approx"
	opt=""
fi

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
			fmode="SMT/Z3"
		else
			fmode="??"
		fi

		echo "\\midrule"
		echo "{\scriptsize \emph{${fmode}:}}"'\\\\'
		cat="$mode"
	fi

	>&2 echo "--- ${name} : ${path} (${mode}) ---"

	printf "${name}"
	./benchone.sh "${name}" "${path}" "${mode}" "${approx}" "${opt}"
	echo '\\\\'
done
