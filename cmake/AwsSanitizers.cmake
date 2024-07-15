# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0.

include(CheckCCompilerFlag)
include(CheckCXXCompilerFlag)

option(ENABLE_SANITIZERS "Enable sanitizers in debug builds" OFF)
set(SANITIZERS "address;undefined" CACHE STRING "List of sanitizers to build with")

# This function checks if a given sanitizer is available.
# Parameters:
#  sanitizer: The sanitizer to check.
#  [out_variable]: The variable to assign the result to. Defaults to HAS_SANITIZER_${sanitizer}.
# Options:
#  IS_CXX: This option switches the function to check the CXX compiler.
function(aws_check_sanitizer sanitizer)
    set(options IS_CXX)
    cmake_parse_arguments(ARG "${options}" "" "" ${ARGN})

    # Determine the number of extra parameters passed to the function.
    list(LENGTH ARG_UNPARSED_ARGUMENTS extra_count)

    if(${extra_count} EQUAL 0)
        # Use the default out variable.
        set(out_variable HAS_SANITIZER_${sanitizer})
        # Sanitize the variable name to remove illegal characters
        string(MAKE_C_IDENTIFIER ${out_variable} out_variable)
    elseif(${extra_count} EQUAL 1)
        # Use the out variable provided by a function caller.
        set(out_variable ${ARG_UNPARSED_ARGUMENTS})
    else()
        message(FATAL_ERROR "Error: aws_check_sanitizer() called with multiple out variables")
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
        if(ARG_IS_CXX)
            check_cxx_compiler_flag(${sanitizer_test_flag} ${out_variable})
        else()
            check_c_compiler_flag(${sanitizer_test_flag} ${out_variable})
        endif()
    else()
        set(${out_variable} 0 PARENT_SCOPE)
    endif()
endfunction()

# This function enables sanitizers on the given target
# Parameters:
#  SANITIZERS: The list of extra sanitizers to enable
# Options:
#  IS_CXX: This option switches the function to check the CXX compiler.
function(aws_add_sanitizers target)
    set(options IS_CXX)
    set(multiValueArgs SANITIZERS)
    cmake_parse_arguments(SANITIZER "${options}" "${oneValueArgs}" "${multiValueArgs}" ${ARGN})

    if (NOT ENABLE_SANITIZERS)
        return()
    endif()

    # A cmake function's option can be forwarded by using a variable with a value set to this option.
    if(SANITIZER_IS_CXX)
        set(is_cxx IS_CXX)
    else()
        set(is_cxx "")
    endif()

    list(APPEND SANITIZER_SANITIZERS ${SANITIZERS})

    foreach(sanitizer IN LISTS SANITIZER_SANITIZERS)

        set(sanitizer_variable HAS_SANITIZER_${sanitizer})
        # Sanitize the variable name to remove illegal characters
        string(MAKE_C_IDENTIFIER ${sanitizer_variable} sanitizer_variable)

        aws_check_sanitizer(${sanitizer} ${sanitizer_variable} ${is_cxx})
        if(${${sanitizer_variable}})
            if (NOT "${PRESENT_SANITIZERS}" STREQUAL "")
                set(PRESENT_SANITIZERS "${PRESENT_SANITIZERS},")
            endif()
            set(PRESENT_SANITIZERS "${PRESENT_SANITIZERS}${sanitizer}")
        endif()
    endforeach()

    if(PRESENT_SANITIZERS)
        target_compile_options(${target} PRIVATE -fno-omit-frame-pointer -fsanitize=${PRESENT_SANITIZERS})
        target_link_libraries(${target} PUBLIC "-fno-omit-frame-pointer -fsanitize=${PRESENT_SANITIZERS}")

        string(REPLACE "," ";" PRESENT_SANITIZERS "${PRESENT_SANITIZERS}")
        set(${target}_SANITIZERS ${PRESENT_SANITIZERS} PARENT_SCOPE)
    endif()
endfunction()
