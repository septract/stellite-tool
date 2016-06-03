#!/bin/bash

for file in $(find ./examples/{"",vbcmn15/}{pass,fail} -iname '*.stl' | sort);
do
  # printf "Stellite> $file... "
  name=`basename $file .stl`
  outfile="./alloy/gen/${name}.als"

  # Run the test. 
  STARTTIME=$(date +%s)
  echo "Stellite> generating ${outfile}"
  ./gentest.sh ${1-7} $file $outfile || exit 1 
  ENDTIME=$(date +%s)
done

