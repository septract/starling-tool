#!/bin/sh
# Usage: countFails.sh path/to/cvf

source setStarling.sh


printf "%s: " "$1"
$STARLING -h $1 |
	grep "fail" |
	cut -d" " -f1 |
	tr "\n" " "
echo
