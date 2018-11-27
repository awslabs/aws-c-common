#!/bin/bash

set -e

mkdir build
cd build

cmake -DPERFORM_HEADER_CHECK=ON -DENABLE_SANITIZERS=ON $@ ../
make
make test

cd ..
