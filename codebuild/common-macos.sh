#!/bin/bash

# Until CodeBuild supports macOS, this script is just used by Travis.

set -e

mkdir build
cd build

cmake -DPERFORM_HEADER_CHECK=ON -DENABLE_SANITIZERS=ON $@ ../
make
make test
