#!/bin/bash
make
Z3DIR=$(ocamlfind query z3)

DIR=$(dirname "$(realpath "$0")")
LD_LIBRARY_PATH=$LD_LIBRARY_PATH:$Z3DIR "$DIR"/_build/default/main.exe "$@"
