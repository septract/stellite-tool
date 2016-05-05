#!/bin/sh

for file in $(find ./examples/{pass,fail} -iname '*.stl' | sort);
do
	echo "$file"
done

