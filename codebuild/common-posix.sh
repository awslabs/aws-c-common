#!/bin/bash

set -e

mkdir /tmp/build
cd /tmp/build

cmake -DPERFORM_HEADER_CHECK=ON -DENABLE_SANITIZERS=ON $@ $CODEBUILD_SRC_DIR
make -j 12
ctest . --output-on-failure
rm -rf ./*
cmake -DPERFORM_HEADER_CHECK=ON -DENABLE_SANITIZER=ON -DBUILD_SHARED_LIBS=ON $@ $CODEBUILD_SRC_DIR
make -j 12
ctest . --output-on-failure

