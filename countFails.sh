#!/bin/sh
# Usage: countFails.sh path/to/cvf

if [ "$(uname)" = "Darwin" ]; then
  STARLING=mono ./bin/Debug/starling.exe
elif [ "$(expr substr $(uname -s) 1 5)" = "Linux" ]; then
  STARLING=mono ./bin/Debug/starling.exe
elif [ "$(expr substr $(uname -s) 1 10)" = "MINGW32_NT" ]; then
  STARLING=./bin/Debug/starling.exe
fi


printf "%s: " "$1"
$STARLING -h $1 |
	grep "fail" |
	cut -d" " -f1 |
	tr "\n" " "
echo
