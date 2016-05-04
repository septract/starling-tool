#!/bin/sh

# Traces a term through all of the term stages.

SED=${SED:-"sed"}

if [ $# != 2 ];
then
	echo "usage: $0 FILE TERM"
	exit 1
fi

echo "Framer:"
./starling.sh -s goalAdd -t "$2" "$1" | $SED "s/^/    /"
echo "TermGen:"
./starling.sh -s termgen -t "$2" "$1" | $SED "s/^/    /"
echo "Reify:"
./starling.sh -s reify -t "$2" "$1" | $SED "s/^/    /"
echo "Flatten:"
./starling.sh -s flatten -t "$2" "$1" | $SED "s/^/    /"
echo "Semantics:"
./starling.sh -s semantics -t "$2" "$1" | $SED "s/^/    /"
echo "Optimise:"
./starling.sh -s termOptimise -t "$2" "$1" | $SED "s/^/    /"
echo "Z3:"
./starling.sh -s z3 -t "$2" "$1" | $SED "s/^/    /"
