#!/bin/bash

FILES=well-typed-syntax.agda # well-typed-syntax-helpers.agda # well-typed-syntax.agda #"well-typed-syntax-helpers.agda well-typed-syntax.agda"

echo > preunused

for j in $FILES; do
    for i in $(grep -o '^ *[^: {}]* [:=]' $j | sed s'/ :$//g' | sed s'/^ *//g'); do
	echo "$i"
	echo "$(grep -h "$i" *.agda | grep '^'"$i"'$\|^'"$i"'[ ()]\|[ (){}]'"$i"'$\|[ (){}]'"$i"'[ ()]' | grep --color=auto "$i" | wc -l): $i" | tee -a preunused
    done
done

cat preunused | sort -n | uniq > unused
rm preunused
