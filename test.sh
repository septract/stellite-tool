#!/bin/sh

for file in $(find ./examples/{pass,fail} -iname '*.stl' | sort);
do
  printf "Checking $file..."
  name=`basename $file .stl`
  TMPFILE=`mktemp /tmp/${name}.XXXXXX` || exit 1 
  ./runtest.sh $file > $TMPFILE 
  if grep -q "OUTCOME" $TMPFILE; then 
       printf "passed\n";  
  else 
       printf "failed\n"; 
  fi  
done

