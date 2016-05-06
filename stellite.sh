#!/bin/sh

if [ "$(uname)" = "Darwin" ]; then
  mono ./bin/Debug/stellite.exe $*
elif [ "$(expr substr $(uname -s) 1 5)" = "Linux" ]; then
  mono ./bin/Debug/stellite.exe $*
elif [ "$(expr substr $(uname -s) 1 10)" = "MINGW32_NT" ]; then
  ./bin/Debug/stellite.exe $*
elif [ "$(expr substr $(uname -s) 1 10)" = "MINGW64_NT" ]; then
  ./bin/Debug/stellite.exe $*
fi
