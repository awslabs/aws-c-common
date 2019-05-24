#!/usr/bin/env bash

# usage:
#   -c, --clean - remove any cached CMake config before building
#   <all other args> - will be passed to cmake as-is

set -e
set -x


home_dir="/tmp"

# where to have cmake put its binaries
build_dir=$home_dir/build/downstream
# where deps will be installed
install_prefix=$build_dir/install

cmake_args=""

function cmake_project {
    local proj_dir=$1
    pushd $proj_dir
    mkdir -p ci-build
    cd ci-build
    cmake -G"Unix Makefiles" $cmake_args -DCMAKE_PREFIX_PATH=$install_prefix -DCMAKE_INSTALL_PREFIX=$install_prefix ..
    cmake --build . --target all
    cmake --build . --target install
    if [[ $cmake_args != *"-DBUILD_TESTING=OFF"* ]]; then
        ctest . --output-on-failure
    fi
    popd
}

function build_project {
    local dep=$1
    local commit_or_branch=$2

    # git clone the repo and build it
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

    cmake_project .

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

# build s2n without tests
if [ "$(uname)" != "Darwin" ]; then
    default_cmake_args=$cmake_args
    cmake_args="$cmake_args -DBUILD_TESTING=OFF"
    build_project s2n e23fb83e80f567c225279cdeb6c9e271b2ff459c
    cmake_args=$default_cmake_args
fi

# build aws-c-common from this pr/branch
cmake_project .

# build master head rev of downstream projects
cd $home_dir
build_project aws-checksums
build_project aws-c-event-stream
build_project aws-c-compression
build_project aws-c-io
build_project aws-c-cal
build_project aws-c-mqtt
build_project aws-c-http
