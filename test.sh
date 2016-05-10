#!/bin/sh

for file in $(find ./examples/{pass,fail} -iname '*.stl' | sort);
do
  printf "Stellite> $file... "
  name=`basename $file .stl`
  TMPFILE=`mktemp /tmp/${name}.XXXXXX` || \
      { echo "Couldn't create temporary file!">&2; exit 1; } 

  # Run the test. 
  STARTTIME=$(date +%s)
  ./runtest.sh $file > $TMPFILE || exit 1 
  ENDTIME=$(date +%s)

  # Check the outcome
  if grep -q "OUTCOME" $TMPFILE; then 
       printf "pass";  
  else 
       printf "fail"; 
  fi  
  printf " ($(($ENDTIME - $STARTTIME)) seconds)\n"
  
  # Detect Alloy warnings 
  if grep -q "Warning:" $TMPFILE; then 
    printf "ALLOY WARNING:\n"
    awk '/Warning/{a=1}/============ Command/{a=0}a' $TMPFILE | sed 's/^/  /' 
  fi 
done

