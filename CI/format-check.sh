#!/usr/bin/env bash

# set -ex

if type clang-format-3.8 2> /dev/null ; then
    CLANG_FORMAT=clang-format-3.8
elif type clang-format 2> /dev/null ; then
    # Clang format found, but need to check version
    CLANG_FORMAT=clang-format
else
    echo "No appropriate clang-format found."
    exit 1
fi

FAIL=0
SOURCE_FILES=`find source include tests -type f -name '*.h' -o -name '*.c'`
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
