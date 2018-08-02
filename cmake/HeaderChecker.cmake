# Copyright 2010-2018 Amazon.com, Inc. or its affiliates. All Rights Reserved.
#
# Licensed under the Apache License, Version 2.0 (the "License").
# You may not use this file except in compliance with the License.
# A copy of the License is located at
#
#  http://aws.amazon.com/apache2.0
#
# or in the "license" file accompanying this file. This file is distributed
# on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
# express or implied. See the License for the specific language governing
# permissions and limitations under the License.

# This cmake logic verifies that each of our headers is complete, in that it
# #includes any necessary dependencies, and that it builds under C++ as well.
# 
# To do so, we generate a single-line C or C++ source file that includes each
# header, and link all of these stub source files into a test executable.

set(HEADER_CHECKER_ROOT "${CMAKE_CURRENT_BINARY_DIR}/header-checker")

set(HEADER_CHECKER_LIB ${CMAKE_PROJECT_NAME}-header-check)
add_executable(${HEADER_CHECKER_LIB} "cmake/header-test-stub.c")
target_link_libraries(${HEADER_CHECKER_LIB} ${CMAKE_PROJECT_NAME})
target_compile_definitions(${HEADER_CHECKER_LIB} PRIVATE AWS_UNSTABLE_TESTING_API=1)

# We want to be able to verify that the proper C++ header guards are in place, so
# build this target as a C++ application
set_target_properties(${HEADER_CHECKER_LIB} PROPERTIES
    LINKER_LANGUAGE CXX
    CXX_STANDARD 11
    CXX_STANDARD_REQUIRED 0
    C_STANDARD 99
)

function(CHECK_HEADERS)
    foreach(header ${ARGV})
        file(RELATIVE_PATH rel_header ${CMAKE_CURRENT_SOURCE_DIR} ${header})
        file(RELATIVE_PATH include_path "${CMAKE_CURRENT_SOURCE_DIR}/include" ${header})
        set(stub_dir "${HEADER_CHECKER_ROOT}/${rel_header}")
        file(MAKE_DIRECTORY "${stub_dir}")
        file(WRITE "${stub_dir}/check.c" "#include <${include_path}>\n")
        file(WRITE "${stub_dir}/checkcpp.cpp" "#include <${include_path}>\n")

        target_sources(${HEADER_CHECKER_LIB} PUBLIC "${stub_dir}/check.c")
        target_sources(${HEADER_CHECKER_LIB} PUBLIC "${stub_dir}/checkcpp.cpp")
    endforeach(header)
endfunction()
