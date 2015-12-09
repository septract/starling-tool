#!/bin/sh

for file in $(find ./Examples -iname '*.cvf');
do
	./countFails.sh "$file"
done
