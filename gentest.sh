#!/bin/bash

if [ $# != 3 ];
then
	echo "usage: $0 DEPTH INFILE OUTFILE"
	exit 1
fi

touch $2 || exit 1; # check that the file is accessible  
./stellite.sh --depth $1 --file $2 > $3 || \
  { echo "Predicate generation failed!">&2 ; exit 1; } 
cat ./alloy/checkTemplate.als >> $3 
