#!/bin/sh

for file in $(find ./Examples -iname '*.cvf' | sort);
do
	./countFails.sh "$file"
done
