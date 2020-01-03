#!/bin/bash
DIR=$(dirname "$(realpath "$0")")
"$DIR"/run.sh -solver OMS -path /home/maria/opti/optiMathSAT/optimathsat-1.6.3-linux-64-bit/bin/optimathsat "$@"
