#!/bin/sh

# Uses dot to produce a graph of the method $2 in file $1.
# Saves as $2.pdf in current directory.

DOT=${DOT:-"dot"}

if [ $# != 2 ];
then
	echo "usage: $0 FILE METHOD"
	exit 1
fi

./starling.sh -s graph -t "$2" "$1" | $DOT -Tpdf > "${2}.pdf"
