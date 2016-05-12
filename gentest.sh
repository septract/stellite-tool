#!/bin/sh

if [ $# != 2 ];
then
	echo "usage: $0 INFILE OUTFILE"
	exit 1
fi

touch $2 || exit 1; # check that the file is accessible  
./stellite.sh --depth 7 --file $1 > $2 || { echo "Predicate generation failed!">&2 ; exit 1; } 
cat ./alloy/checkTemplate.als >> $2 
