#!/bin/bash
# à utiliser sur un fichier modèle retourné par glucose ou minisat
printf "+---+---+---+\n|"

i=1 # numéro d'entrée courante
for n in `grep -v 'SAT' $1 | sed -e 's/-[0-9]* //g;s/ 0//g;s/[1-9][1-9]\([1-9]\)/\1/g' | sort`
do
    printf "$n"
    if !(( i % 3 ))
    then
        printf "|"
    fi
    if !(( i % 9 ))
    then
        printf "\n"
    fi
    if !((i % 27))
    then
        echo "+---+---+---+"
    fi
    if !(( i % 9 )) && (( i < 81 ))
    then
        printf "|"
    fi
    i=$((i+1))
done
