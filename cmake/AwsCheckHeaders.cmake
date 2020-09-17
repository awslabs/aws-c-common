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

function(aws_check_headers_internal target lang std)
    if (${lang} STREQUAL CXX)
        set (FILE_EXT cpp)
    else ()
        set (FILE_EXT c)
    endif ()

    set(HEADER_CHECKER_LIB "${target}-header-check-${lang}-${std}")
    set(HEADER_CHECKER_ROOT "${CMAKE_CURRENT_BINARY_DIR}/${HEADER_CHECK_LIB}")

    # Write stub main file
    set(HEADER_CHECKER_MAIN "${HEADER_CHECKER_ROOT}/stub.${FILE_EXT}")
    file(WRITE ${HEADER_CHECKER_MAIN} "
        int main(int argc, char **argv) {
            (void)argc;
            (void)argv;

            return 0;
        }")

    add_executable(${HEADER_CHECKER_LIB} ${HEADER_CHECKER_MAIN})
    target_link_libraries(${HEADER_CHECKER_LIB} ${target})
    target_compile_definitions(${HEADER_CHECKER_LIB} PRIVATE AWS_UNSTABLE_TESTING_API=1 AWS_HEADER_CHECKER=1)

    set_target_properties(${HEADER_CHECKER_LIB} PROPERTIES
        LINKER_LANGUAGE ${lang}
        "${lang}_STANDARD" ${std}
    )

    foreach(header IN LISTS ARGN)
        if (NOT ${header} MATCHES "\\.inl$")
            file(RELATIVE_PATH rel_header ${CMAKE_HOME_DIRECTORY} ${header})
            file(RELATIVE_PATH include_path "${CMAKE_HOME_DIRECTORY}/include" ${header})
            set(stub_dir "${HEADER_CHECKER_ROOT}/${rel_header}")
            file(MAKE_DIRECTORY "${stub_dir}")
            file(WRITE "${stub_dir}/check.${FILE_EXT}" "#include <${include_path}>\n")

            target_sources(${HEADER_CHECKER_LIB} PUBLIC "${stub_dir}/check.${FILE_EXT}")
        endif()
    endforeach(header)
endfunction()

# Check headers with each supported C_STANDARD:
# https://cmake.org/cmake/help/latest/prop_tgt/C_STANDARD.html
# Note that while aws-c-*** libs are built with c99, their headers should be includable in anything c90 and up.
# Call as: aws_check_headers_c(${target} HEADERS TO CHECK LIST)
function(aws_check_headers_c target)
    if (PERFORM_HEADER_CHECK)
        aws_check_headers_internal(${target} C 90 ${ARGN})
        aws_check_headers_internal(${target} C 99 ${ARGN})
        aws_check_headers_internal(${target} C 11 ${ARGN})
    endif ()
endfunction()

# Check headers with each supported CXX_STANDARD:
# https://cmake.org/cmake/help/latest/prop_tgt/CXX_STANDARD.html
# Call as: aws_check_headers_cxx(${target} HEADERS TO CHECK LIST)
function(aws_check_headers_cxx target)
    if (PERFORM_HEADER_CHECK)
        aws_check_headers_internal(${target} CXX 11 ${ARGN})
        aws_check_headers_internal(${target} CXX 14 ${ARGN})
        aws_check_headers_internal(${target} CXX 17 ${ARGN})
        aws_check_headers_internal(${target} CXX 20 ${ARGN})
    endif ()
endfunction()

# Check headers with each supported C_STANDARD and CXX_STANDARD
# Call as: aws_check_headers(${target} HEADERS TO CHECK LIST)
function(aws_check_headers target)
    if (PERFORM_HEADER_CHECK)
        aws_check_headers_c(${target} ${ARGN})
        aws_check_headers_cxx(${target} ${ARGN})
    endif ()
endfunction()
