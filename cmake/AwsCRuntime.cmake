# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0.

# This function enables sanitizers on the given target
# Options:
#  SANITIZERS: The list of extra sanitizers to enable
#  BLACKLIST: The blacklist file to use (passed to -fsanitizer-blacklist=)
function(aws_determine_local_c_runtime target)
    if (CMAKE_SYSTEM_NAME STREQUAL "Linux")
        execute_process(COMMAND "ldd" "--version" OUTPUT_VARIABLE AWS_LDD_OUTPUT ERROR_VARIABLE AWS_LDD_OUTPUT)
        string(FIND "${AWS_LDD_OUTPUT}" "musl" AWS_MUSL_INDEX)
        string(FIND "${AWS_LDD_OUTPUT}" "GLIBC" AWS_GLIBC_INDEX)
        if (NOT(${AWS_MUSL_INDEX} EQUAL -1))
            message(STATUS "MUSL libc detected")
            set(${target} "musl" PARENT_SCOPE)
        else()
            if (NOT(${AWS_GLIBC_INDEX} EQUAL -1))
                message(STATUS "Gnu libc detected")
            else()
                message(STATUS "Could not determine C runtime, defaulting to gnu libc")
            endif()
            set(${target} "glibc" PARENT_SCOPE)
        endif()
    else()
        set(${target} "cruntime" PARENT_SCOPE)
    endif()
endfunction()
