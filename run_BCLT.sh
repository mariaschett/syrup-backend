#!/bin/bash
DIR=$(dirname "$(realpath "$0")")
"$DIR"/run.sh -solver BCLT -path /home/maria/opti/EBSO/implementation/barcelogic "$@"
