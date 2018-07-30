#!/bin/bash

mkdir build
cd build

cmake -DENABLE_SANITIZERS=ON $@ ../ || exit 1
make || exit 1
make test || exit 1

cd ..

./cppcheck.sh || exit 1
