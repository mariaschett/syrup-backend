#!/bin/bash
DIR=$(dirname "$(realpath "$0")")
"$DIR"/run.sh -solver OMS -path solvers/optimathsat  "$@"
