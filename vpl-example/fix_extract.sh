#!/bin/bash
# insert "open Vpl" at the head of extracted files 
# this hack is necessary because the lack of a limitation of coq extraction on library.

HEAD="open Vpl"

function myfix() {
    if ! [ -f $1 ]; then
        echo "ERROR: $1 does not exist"
        exit 1
    fi
    if !(head -1 $1 | grep -q "${HEAD}"); then
        echo "fix $1"
        mv $1 tmp.$$
        echo "${HEAD}" > $1
        cat tmp.$$ >> $1
        rm -f tmp.$$
    fi
}

for f in "$@" ; do
    myfix "${f}" || exit 1
done
