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
    list(LENGTH ARGN extra_count)
    if(${extra_count} EQUAL 0)
        set(out_variable HAS_SANITIZER_${sanitizer})
        # Sanitize the variable name to remove illegal characters
        string(MAKE_C_IDENTIFIER ${out_variable} out_variable)
    elseif(${extra_count} EQUAL 1)
        set(out_variable ${ARGN})
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
        set(sanitizer_flags -fno-omit-frame-pointer -fsanitize=${PRESENT_SANITIZERS})

        # By default UBSan only prints a diagnostic and continues. Turn violations into hard failures so
        # they surface as test errors rather than being silently recovered from.
        if("${PRESENT_SANITIZERS}" MATCHES "undefined")
            list(APPEND sanitizer_flags -fno-sanitize-recover=all)
        endif()

        target_compile_options(${target} PRIVATE ${sanitizer_flags})
        string(REPLACE ";" " " sanitizer_link_flags "${sanitizer_flags}")
        target_link_libraries(${target} PUBLIC "${sanitizer_link_flags}")

        string(REPLACE "," ";" PRESENT_SANITIZERS "${PRESENT_SANITIZERS}")
        set(${target}_SANITIZERS ${PRESENT_SANITIZERS} PARENT_SCOPE)
    endif()
endfunction()
