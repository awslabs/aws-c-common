# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0.

include(AwsCFlags)
include(AwsSanitizers)

option(ENABLE_NET_TESTS "Run tests requiring an internet connection." ON)

# Maintain a global list of AWS_TEST_CASES
define_property(GLOBAL PROPERTY AWS_TEST_CASES BRIEF_DOCS "Test Cases" FULL_DOCS "Test Cases")
set(AWS_TEST_CASES "" CACHE INTERNAL "Test cases valid for this configuration")

# Registers a test case by name (the first argument to the AWS_TEST_CASE macro in aws_test_harness.h)
macro(add_test_case name)
    list(APPEND TEST_CASES "${name}")
    list(APPEND AWS_TEST_CASES "${name}")
    set_property(GLOBAL PROPERTY AWS_TEST_CASES ${AWS_TEST_CASES})
endmacro()

# Like add_test_case, but for tests that require a working internet connection.
macro(add_net_test_case name)
    if (ENABLE_NET_TESTS)
        list(APPEND TEST_CASES "${name}")
        list(APPEND AWS_TEST_CASES "${name}")
        set_property(GLOBAL PROPERTY AWS_TEST_CASES ${AWS_TEST_CASES})
    endif()
endmacro()

# Generate a test driver executable with the given name
function(generate_test_driver driver_exe_name)
    create_test_sourcelist(test_srclist test_runner.c ${TEST_CASES})
    # Write clang tidy file that disables all but one check to avoid false positives
    file(WRITE "${CMAKE_CURRENT_BINARY_DIR}/.clang-tidy" "Checks: '-*,misc-static-assert'")

    add_executable(${driver_exe_name} ${CMAKE_CURRENT_BINARY_DIR}/test_runner.c ${TESTS})
    aws_set_common_properties(${driver_exe_name} NO_WEXTRA NO_PEDANTIC)

    if (NOT MSVC AND AWS_SHOULD_DISABLE_STRINGOP_OVERFLOW)
        SET_SOURCE_FILES_PROPERTIES(test_runner.c PROPERTIES COMPILE_FLAGS -Wno-error=stringop-overflow)
    endif()

    aws_add_sanitizers(${driver_exe_name} ${${PROJECT_NAME}_SANITIZERS})

    target_link_libraries(${driver_exe_name} PRIVATE ${PROJECT_NAME})

    set_target_properties(${driver_exe_name} PROPERTIES LINKER_LANGUAGE C C_STANDARD 99)
    if (MSVC)
        if(STATIC_CRT)
            target_compile_options(${driver_exe_name} PRIVATE "/MT$<$<CONFIG:Debug>:d>")
        else()
            target_compile_options(${driver_exe_name} PRIVATE "/MD$<$<CONFIG:Debug>:d>")
        endif()
    endif()
    target_compile_definitions(${driver_exe_name} PRIVATE AWS_UNSTABLE_TESTING_API=1)
    target_include_directories(${driver_exe_name} PRIVATE ${CMAKE_CURRENT_LIST_DIR})

    foreach(name IN LISTS TEST_CASES)
        add_test(${name} ${driver_exe_name} "${name}")
    endforeach()

    # Clear test cases in case another driver needsto be generated
    unset(TEST_CASES PARENT_SCOPE)
endfunction()

function(generate_cpp_test_driver driver_exe_name)
    create_test_sourcelist(test_srclist test_runner.cpp ${TEST_CASES})

    add_executable(${driver_exe_name} ${CMAKE_CURRENT_BINARY_DIR}/test_runner.cpp ${TESTS})
    target_link_libraries(${driver_exe_name} PRIVATE ${PROJECT_NAME})

    set_target_properties(${driver_exe_name} PROPERTIES LINKER_LANGUAGE CXX)
    if (MSVC)
        if(STATIC_CRT)
            target_compile_options(${driver_exe_name} PRIVATE "/MT$<$<CONFIG:Debug>:d>")
        else()
            target_compile_options(${driver_exe_name} PRIVATE "/MD$<$<CONFIG:Debug>:d>")
        endif()
    endif()
    target_compile_definitions(${driver_exe_name} PRIVATE AWS_UNSTABLE_TESTING_API=1)
    target_include_directories(${driver_exe_name} PRIVATE ${CMAKE_CURRENT_LIST_DIR})

    foreach(name IN LISTS TEST_CASES)
        add_test(${name} ${driver_exe_name} "${name}")
    endforeach()

    # Clear test cases in case another driver needsto be generated
    unset(TEST_CASES PARENT_SCOPE)
endfunction()
