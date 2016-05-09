#!/bin/sh

if [ $# != 1 ];
then
	echo "usage: $0 FILE"
	exit 1
fi

if [ ${1: -4} != ".stl" ]
then 
    echo "Bad input filename: $1 - should end with .stl" 
    exit 1
fi 

outfile="./alloy/gen/$(basename $1 .stl).als"
./gentest.sh $1 $outfile || exit 1 

java -Xmx2048m -cp ./alloy-mod.jar \
      edu.mit.csail.sdg.alloy4whole.ExampleUsingTheCompiler \
      $outfile  


