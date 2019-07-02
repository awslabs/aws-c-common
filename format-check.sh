#!/usr/bin/env bash

if [[ -z $CLANG_FORMAT ]] ; then
    CLANG_FORMAT=clang-format
fi

if NOT type $CLANG_FORMAT 2> /dev/null ; then
    echo "No appropriate clang-format found."
    exit 1
fi

FAIL=0
SOURCE_FILES=`find source include tests .cbmc-batch -type f \( -name '*.h' -o -name '*.c' -o -name '*.inl' \)`
for i in $SOURCE_FILES
do
    $CLANG_FORMAT -output-replacements-xml $i | grep -c "<replacement " > /dev/null
    if [ $? -ne 1 ]
    then
        echo "$i failed clang-format check."
        FAIL=1
    fi
done

exit $FAIL
