#!/bin/bash

set -e

mkdir /tmp/build
cd /tmp/build

CMAKE_ARGS="-DCMAKE_BUILD_TYPE=RelWithDebInfo -DPERFORM_HEADER_CHECK=ON -DENABLE_SANITIZERS=ON $@"
cmake $CMAKE_ARGS  $CODEBUILD_SRC_DIR
make -j
ctest . --output-on-failure
rm -rf ./*
cmake  -DBUILD_SHARED_LIBS=ON $CMAKE_ARGS $CODEBUILD_SRC_DIR
make -j
ctest . --output-on-failure

