#!/bin/sh

for file in $(find ./examples/{pass,fail} -iname '*.stl' | sort);
do
  printf "Stellite> $file... "
  name=`basename $file .stl`
  TMPFILE=`mktemp /tmp/${name}.XXXXXX` || \
      { echo "Couldn't create temporary file!">&2; exit 1; } 
  STARTTIME=$(date +%s)
  ./runtest.sh $file > $TMPFILE || exit 1 
  ENDTIME=$(date +%s)
  if grep -q "OUTCOME" $TMPFILE; then 
       printf "pass";  
  else 
       printf "fail"; 
  fi  
  printf " ($(($ENDTIME - $STARTTIME)) seconds)\n"
done

