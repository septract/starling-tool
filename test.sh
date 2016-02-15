#!/bin/sh

for file in $(find ./Examples/{Pass,Fail} -iname '*.cvf' | sort);
do
	./countFails.sh "$file"
done
