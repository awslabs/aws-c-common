#!/bin/sh -x

set -e

cppcheck                                                    \
                                                            \
--enable=all --std=c99 --language=c                         \
--template='[{file}:{line}]: ({severity},{id}){message}'    \
--force --error-exitcode=-1                                 \
                                                            \
-I include                                                  \
-USELF_TEST  -UCLOCK_MONOTONIC_RAW                          \
                                                            \
--suppress=unusedFunction                                   \
--suppress=missingInclude                                   \
--suppress=memleak:tests/hash_table_test.c                  \
--suppress=staticStringCompare:tests/assert_test.c          \
--suppress=*:build/tests/test_runner.c                      \
                                                            \
-q .
