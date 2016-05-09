#!/bin/sh

for file in $(find ./examples/{pass,fail} -iname '*.stl' | sort);
do
  printf ">> $file... "
  name=`basename $file .stl`
  TMPFILE=`mktemp /tmp/${name}.XXXXXX` || \
      { echo "Couldn't create temporary file!">&2; exit 1; } 
  ./runtest.sh $file > $TMPFILE || exit 1 
  if grep -q "OUTCOME" $TMPFILE; then 
       printf "pass\n";  
  else 
       printf "fail\n"; 
  fi  
done

