# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0.

# This cmake logic verifies that each of our headers is complete, in that it
# #includes any necessary dependencies, and that it builds under C++ as well.
#
# To do so, we generate a single-line C or C++ source file that includes each
# header, and link all of these stub source files into a test executable.

option(PERFORM_HEADER_CHECK "Performs compile-time checks that each header can be included independently. Requires a C++ compiler.")

if (PERFORM_HEADER_CHECK)
    enable_language(CXX)
endif()

# Call as: aws_check_headers(${target} HEADERS TO CHECK LIST)
function(aws_check_headers target)
    if (PERFORM_HEADER_CHECK)

        set(HEADER_CHECKER_ROOT "${CMAKE_CURRENT_BINARY_DIR}/header-checker")

        # Write stub main file
        set(HEADER_CHECKER_MAIN "${HEADER_CHECKER_ROOT}/headerchecker_main.c")
        file(WRITE ${HEADER_CHECKER_MAIN} "
            int main(int argc, char **argv) {
                (void)argc;
                (void)argv;

                return 0;
            }\n")

        set(HEADER_CHECKER_LIB ${target}-header-check)
        add_executable(${HEADER_CHECKER_LIB} ${HEADER_CHECKER_MAIN})
        target_link_libraries(${HEADER_CHECKER_LIB} ${target})
        target_compile_definitions(${HEADER_CHECKER_LIB} PRIVATE AWS_UNSTABLE_TESTING_API=1 AWS_HEADER_CHECKER=1)

        # We want to be able to verify that the proper C++ header guards are in place, so
        # build this target as a C++ application
        set_target_properties(${HEADER_CHECKER_LIB} PROPERTIES
            LINKER_LANGUAGE CXX
            CXX_STANDARD 11
            CXX_STANDARD_REQUIRED 0
            C_STANDARD 99
        )

        # Ensure our headers can be included by an application with its warnings set very high
        if(MSVC)
            target_compile_options(${HEADER_CHECKER_LIB} PRIVATE /Wall /WX)
        else()
            target_compile_options(${HEADER_CHECKER_LIB} PRIVATE -Wall -Wextra -Wpedantic -Werror)
        endif()

        foreach(header IN LISTS ARGN)
            if (NOT ${header} MATCHES "\\.inl$")
                # create unique token for this file, e.g.:
                # "${CMAKE_CURRENT_SOURCE_DIR}/include/aws/common/byte_buf.h" -> "aws_common_byte_buf_h"
                file(RELATIVE_PATH include_path "${CMAKE_CURRENT_SOURCE_DIR}/include" ${header})
                # replace non-alphanumeric characters with underscores
                string(REGEX REPLACE "[^a-zA-Z0-9]" "_" unique_token ${include_path})
                set(c_file "${HEADER_CHECKER_ROOT}/headerchecker_${unique_token}.c")
                set(cpp_file "${HEADER_CHECKER_ROOT}/headerchecker_${unique_token}.cpp")
                # include header twice to check for include-guards
                # define a unique int or compiler complains that there's nothing in the file
                file(WRITE "${c_file}" "#include <${include_path}>\n#include <${include_path}>\nint ${unique_token}_c;\n")
                file(WRITE "${cpp_file}" "#include <${include_path}>\n#include <${include_path}>\nint ${unique_token}_cpp;")

                target_sources(${HEADER_CHECKER_LIB} PUBLIC "${c_file}" "${cpp_file}")
            endif()
        endforeach(header)
    endif() # PERFORM_HEADER_CHECK
endfunction()
