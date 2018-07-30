#!/bin/bash

# Until CodeBuild supports macOS, this script is just used by Travis.

mkdir build
cd build

cmake -DENABLE_SANITIZERS=ON $@ ../ || exit 1
make || exit 1
make test || exit 1
