#!/bin/bash

set -e

mkdir /tmp/build
cd /tmp/build

cmake -DCMAKE_BUILD_TYPE=Release -DTARGET_ARCH=ANDROID -DCMAKE_TOOLCHAIN_FILE=/opt/android-ndk/build/cmake/android.toolchain.cmake -DANDROID_NATIVE_API_LEVEL=19 -DANDROID_NDK=/opt/android-ndk -DANDROID_ABI=arm64-v8a $@ $CODEBUILD_SRC_DIR
make -j
