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
        set(HEADER_CHECKER_MAIN "${HEADER_CHECKER_ROOT}/stub.c")
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
            C_STANDARD 99 # TODO ???
        )

        # Max out warnings
        if(MSVC)
            target_compile_options(${HEADER_CHECKER_LIB} PRIVATE /Wall /WX)
        else()
            target_compile_options(${HEADER_CHECKER_LIB} PRIVATE -Wall -Wextra -Wpedantic -Werror)
        endif()

        foreach(header IN LISTS ARGN)
            if (NOT ${header} MATCHES "\\.inl$")
                file(RELATIVE_PATH rel_header ${CMAKE_CURRENT_SOURCE_DIR} ${header})
                file(RELATIVE_PATH include_path "${CMAKE_CURRENT_SOURCE_DIR}/include" ${header})
                set(stub_dir "${HEADER_CHECKER_ROOT}/${rel_header}")
                file(MAKE_DIRECTORY "${stub_dir}")
                # compiler complains if there's nothing in the file
                # so add an int with a unique name (based on header's path)
                string(REGEX REPLACE "[^a-zA-Z0-9]" "_" unique_token ${include_path})
                # include header twice to check for include-guards
                file(WRITE "${stub_dir}/check.c" "#include <${include_path}>\n#include <${include_path}>\nint ${unique_token}_c;\n")
                file(WRITE "${stub_dir}/checkcpp.cpp" "#include <${include_path}>\n#include <${include_path}>\nint ${unique_token}_cpp;")

                target_sources(${HEADER_CHECKER_LIB} PUBLIC "${stub_dir}/check.c" "${stub_dir}/checkcpp.cpp")
            endif()
        endforeach(header)
    endif() # PERFORM_HEADER_CHECK
endfunction()
