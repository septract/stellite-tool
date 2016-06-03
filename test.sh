#!/bin/sh

for file in $(find ./examples/{"",vbcmn15/}{pass,fail} -iname '*.stl' | sort);
do
  # printf "Stellite> $file... "
  name=`basename $file .stl`
  TMPFILE=`mktemp /tmp/${name}.XXXXXX` || \
      { echo "Couldn't create temporary file!">&2; exit 1; } 

  # Run the test. 
  STARTTIME=$(date +%s)
  ./runtest.sh ${1-7} $file > $TMPFILE || exit 1 
  ENDTIME=$(date +%s)

  # Check the outcome
  if grep -q "OUTCOME" $TMPFILE; then 
       printf "Stellite> %-40s pass" $file;  
  else 
       printf "Stellite> %-40s fail" $file;  
  fi  
  printf " ($(($ENDTIME - $STARTTIME)) secs)\n"
  
  # Detect Alloy warnings 
  if grep -q "Warning:" $TMPFILE; then 
    printf "ALLOY WARNING:\n"
    awk '/Warning/{a=1}/============ Command/{a=0}a' $TMPFILE | sed 's/^/  /' 
  fi 
done

