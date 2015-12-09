#!/bin/sh
# Usage: countFails.sh path/to/cvf

printf "%s: " "$1"
mono ./bin/Debug/starling.exe -h $1 |
	grep "fail" |
	cut -d" " -f1 |
	tr "\n" " "
echo
