# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0.

include(CheckCCompilerFlag)

option(ENABLE_SANITIZERS "Enable sanitizers in debug builds" OFF)
set(SANITIZERS "address;undefined" CACHE STRING "List of sanitizers to build with")

# This function checks if a sanitizer is available
# Options:
#  sanitizer: The sanitizer to check
#  out_variable: The variable to assign the result to. Defaults to HAS_SANITIZER_${sanitizer}
function(aws_check_sanitizer sanitizer)

    if(NOT ${ARGN})
        set(out_variable "${ARGN}")
    else()
        set(out_variable HAS_SANITIZER_${sanitizer})
        # Sanitize the variable name to remove illegal characters
        string(MAKE_C_IDENTIFIER ${out_variable} out_variable)
    endif()

    if(ENABLE_SANITIZERS)
        # When testing for libfuzzer, if attempting to link there will be 2 mains
        if(${sanitizer} STREQUAL "fuzzer")
            set(sanitizer_test_flag -fsanitize=fuzzer-no-link)
        else()
            set(sanitizer_test_flag -fsanitize=${sanitizer})
        endif()

        # Need to set this here so that the flag is passed to the linker
        set(CMAKE_REQUIRED_FLAGS ${sanitizer_test_flag})
        check_c_compiler_flag(${sanitizer_test_flag} ${out_variable})
    else()
        set(${out_variable} 0 PARENT_SCOPE)
    endif()
endfunction()

# This function enables sanitizers on the given target
# Options:
#  SANITIZERS: The list of extra sanitizers to enable
function(aws_add_sanitizers target)
    set(multiValueArgs SANITIZERS)
    cmake_parse_arguments(SANITIZER "" "${oneValueArgs}" "${multiValueArgs}" ${ARGN})

    if (NOT ENABLE_SANITIZERS)
        return()
    endif()

    list(APPEND SANITIZER_SANITIZERS ${SANITIZERS})

    foreach(sanitizer IN LISTS SANITIZER_SANITIZERS)

        set(sanitizer_variable HAS_SANITIZER_${sanitizer})
        # Sanitize the variable name to remove illegal characters
        string(MAKE_C_IDENTIFIER ${sanitizer_variable} sanitizer_variable)

        aws_check_sanitizer(${sanitizer} ${sanitizer_variable})
        if(${${sanitizer_variable}})
            if (NOT "${PRESENT_SANITIZERS}" STREQUAL "")
                set(PRESENT_SANITIZERS "${PRESENT_SANITIZERS},")
            endif()
            set(PRESENT_SANITIZERS "${PRESENT_SANITIZERS}${sanitizer}")
        endif()
    endforeach()

    if(PRESENT_SANITIZERS)
        if(MSVC)
            if(AWS_ARCH_INTEL_X64)
                target_compile_options(${target} PRIVATE -fsanitize=${PRESENT_SANITIZERS})
                target_link_libraries(${target} PRIVATE clang_rt.asan_dynamic-x86_64 clang_rt.asan_dynamic_runtime_thunk-x86_64)
            else()
                message("On Win platforms sanitizer is only supported on x86-64")
                return()
            endif()
        else()
            target_compile_options(${target} PRIVATE -fno-omit-frame-pointer -fsanitize=${PRESENT_SANITIZERS})
            target_link_libraries(${target} PUBLIC "-fsanitize=${PRESENT_SANITIZERS}")
        endif()

        string(REPLACE "," ";" PRESENT_SANITIZERS "${PRESENT_SANITIZERS}")
        set(${target}_SANITIZERS ${PRESENT_SANITIZERS} PARENT_SCOPE)
    endif()
endfunction()
