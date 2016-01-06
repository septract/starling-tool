#!/bin/sh

if [ "$(uname)" = "Darwin" ]; then
  STARLING=mono ./bin/Debug/starling.exe
elif [ "$(expr substr $(uname -s) 1 5)" = "Linux" ]; then
  STARLING=mono ./bin/Debug/starling.exe
elif [ "$(expr substr $(uname -s) 1 10)" = "MINGW32_NT" ]; then
  STARLING=./bin/Debug/starling.exe
fi
