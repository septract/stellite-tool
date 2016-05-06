#!/bin/sh

if [ $# != 2 ];
then
	echo "usage: $0 INFILE OUTFILE"
	exit 1
fi

./stellite.sh $1 > $2 || { echo "Predicate generation failed!">&2 ; exit 1; } 
cat ./alloy/checkTemplate.als >> $2 
