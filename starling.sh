#!/bin/sh

if [ "$(uname)" = "Darwin" ] || [ "$(uname)" = "FreeBSD" ]; then
  mono ./bin/Debug/starling.exe $*
elif [ "$(expr substr $(uname -s) 1 5)" = "Linux" ]; then
  mono ./bin/Debug/starling.exe $*
elif [ "$(expr substr $(uname -s) 1 10)" = "MINGW32_NT" ]; then
  ./bin/Debug/starling.exe $*
elif [ "$(expr substr $(uname -s) 1 10)" = "MINGW64_NT" ]; then
  ./bin/Debug/starling.exe $*
fi
