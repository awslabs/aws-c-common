#!/bin/bash

set -e

mkdir build
cd build

cmake -DENABLE_SANITIZERS=ON $@ ../
make
make test

cd ..

./cppcheck.sh
