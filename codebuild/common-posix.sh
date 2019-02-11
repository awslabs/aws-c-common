#!/bin/bash

set -e

mkdir /tmp/build
cd /tmp/build

cmake -DPERFORM_HEADER_CHECK=ON -DENABLE_SANITIZERS=ON $@ $CODEBUILD_SRC_DIR
make
ctest . --output-on-failure

cd ..
