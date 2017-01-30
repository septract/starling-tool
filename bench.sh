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
sed -e 's/#.*$//' -e '/^$/d' ./benchmarks.in | while read name path spl; do
	if [ -n "${spl}" ];
	then
		fmode="GRASShopper"
	else
		fmode="SMT/Z3"
	fi

	# Print backend header if we're on a new backend.
	if [ "${fmode}" != "${cat}" ];
	then
		echo "\\midrule"
		echo "{\scriptsize \emph{${fmode}:}}"'\\\\'
		cat="$fmode"
	fi

	>&2 echo "--- ${name} : ${path} (${fmode}) ---"

	printf "${name}"
	./benchone.sh "${name}" "${path}" "${spl}" "${approx}" "${opt}"
	echo '\\\\'
done
