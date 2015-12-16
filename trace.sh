#!/bin/sh

# Uses some careful sed-ing to trace a term through all of the term stages
# (frame, termgen, reify, Z3 reify).

STARLING="./bin/Debug/starling.exe"

if [ $# != 2 ];
then
	echo "usage: $0 FILE TERM"
	exit 1
fi

# The sed pattern to use to filter.
# Ugly, but does the job.
#
# Theory: select everything between $2: and the next numeric heading.
# Then, delete the numeric headings.
PATTERN="/^$2:/,/^[0-9][0-9]*:/ {/^[0-9][0-9]*:/d; p}"

echo "Framer:"
mono $STARLING -hF $1 | sed -n "$PATTERN"
echo "TermGen:"
mono $STARLING -hT $1 | sed -n "$PATTERN"
echo "Reify:"
mono $STARLING -hr $1 | sed -n "$PATTERN"
echo "Z3:"
mono $STARLING -hR $1 | sed -n "$PATTERN"
