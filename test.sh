#!/bin/bash

TIMEOUT=3600

for file in $(find ./examples/{"",vbcmn15/}{pass,fail} -iname '*.stl' | sort);
do
  name=$(basename $file .stl)
  TMPFILE=$(mktemp /tmp/${name}.XXXXXX) || \
      { echo "Couldn't create temporary file!">&2; exit 1; } 

  printf "Stellite> %-40s " $file;

  # Run the test. 
  STARTTIME=$(date +%s)
  timeout --foreground $TIMEOUT ./runtest.sh ${1-7} $file > $TMPFILE || exit 1
  CMDRES=$?
  ENDTIME=$(date +%s)

  # Check the outcome
  if [ $CMDRES -eq 124 ]; then 
    printf "Timed out\n"; 
  elif grep -q "OUTCOME" $TMPFILE; then 
    printf "Pass";  
    printf " ($(($ENDTIME - $STARTTIME)) secs)\n"
  else 
    printf "Fail";  
    printf " ($(($ENDTIME - $STARTTIME)) secs)\n"
  fi  
  
  # Detect Alloy warnings 
  if grep -q "Warning:" $TMPFILE; then 
    printf "ALLOY WARNING:\n"
    awk '/Warning/{a=1}/============ Command/{a=0}a' $TMPFILE | sed 's/^/  /' 
  fi 
done

