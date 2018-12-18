#!/usr/bin/env bash

# usage:
#   -c, --clean - remove any cached CMake config before building
#   <all other args> - will be passed to cmake as-is

set -e
set -x

# everything is relative to the directory this script is in
home_dir="$( cd "$( dirname "${BASH_SOURCE[0]}" )" >/dev/null && pwd )"

# where to have cmake put its binaries
build_dir=$home_dir/build/downstream
# where deps will be installed
install_prefix=$build_dir/install

cmake_args=""

function build_project {
    local dep=$1
    local commit_or_branch=$2

    # if the local deps are preferred and the local dep exists, use it
    if [ $prefer_local_deps -ne 0 ] && [ -d "$home_dir/../$dep" ]; then
        pushd $home_dir/../$dep
        echo "Using local repo: $home_dir/../$dep branch:" `git branch | grep \* | cut -d ' ' -f2` "commit: " `git rev-parse HEAD`
    else # git clone the repo and build it
        pushd $build_dir
        if [ -d $dep ]; then
            cd $dep
            git pull --rebase
        else
            git clone https://github.com/awslabs/$dep.git
            cd $dep
        fi

        if [ -n "$commit_or_branch" ]; then
            git checkout $commit_or_branch
        fi
        echo "Using git repo: $dep branch:" `git branch | grep \* | cut -d ' ' -f2` "commit: " `git rev-parse HEAD`
    fi

    mkdir -p dep-build
    cd dep-build

    cmake -G"Unix Makefiles" $cmake_args -DCMAKE_INSTALL_PREFIX=$install_prefix ..
    cmake --build . --target all
    cmake --build . --target install
    cmake --build . --target test

    popd
}

cmake_args=()
while [[ $# -gt 0 ]]
do
    arg="$1"

    case $arg in
        -c|--clean)
        clean=1
        shift
        ;;
        *)    # everything else
        cmake_args="$cmake_args $arg" # unknown args are passed to cmake
        shift
        ;;
    esac
done

if [ $clean ]; then
    rm -rf $build_dir
fi
mkdir -p $build_dir

build_project aws-c-common
build_project aws-checksums
build_project aws-c-event-stream
if [ "$(uname)" != "Darwin"]; then
    build_project s2n
fi
build_project aws-c-io
build_project aws-c-mqtt
