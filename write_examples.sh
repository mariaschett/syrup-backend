#!/bin/bash

for fn in `find examples/ -name input.json`
do
    ./run.sh -solver Z3 $fn -write-only
done
	  
