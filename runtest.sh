#!/bin/sh

if [ $# != 2 ];
then
	echo "usage: $0 DEPTH FILE"
	exit 1
fi

if [ ${2: -4} != ".stl" ]
then 
    echo "Bad input filename: $2 - should end with .stl" 
    exit 1
fi 

outfile="./alloy/gen/$(basename $2 .stl).als"
./gentest.sh $1 $2 $outfile || exit 1 

java -Xmx4096m -cp ./alloy-mod.jar \
      edu.mit.csail.sdg.alloy4whole.ExampleUsingTheCompiler \
      $outfile  


