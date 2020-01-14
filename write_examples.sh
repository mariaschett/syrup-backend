#!/bin/bash

for fn in `find examples/ -name input.json`
do
    ./run.sh $fn -write-only -solver Z3
    ./run.sh $fn -write-only -solver BCLT
    ./run.sh $fn -write-only -solver OMS
done
	  
