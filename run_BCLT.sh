#!/bin/bash
DIR=$(dirname "$(realpath "$0")")
"$DIR"/run.sh -solver BCLT -path solvers/barcelogic "$@"
