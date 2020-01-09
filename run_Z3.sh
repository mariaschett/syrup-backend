#!/bin/bash
DIR=$(dirname "$(realpath "$0")")
"$DIR"/run.sh -solver Z3 -path "$DIR"/solvers/z3 "$@"
