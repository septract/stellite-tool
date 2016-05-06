#!/bin/sh

if [ $# != 2 ];
then
	echo "usage: $0 INFILE OUTFILE"
	exit 1
fi

echo "Generating $2"
./stellite.sh $1 > $2 || { echo "generation failed!" ; exit 1; } 
cat ./alloy/checkTemplate.als >> $2 
