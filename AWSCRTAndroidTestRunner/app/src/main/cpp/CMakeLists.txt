# For more information about using CMake with Android Studio, read the
# documentation: https://d.android.com/studio/projects/add-native-code.html

# Sets the minimum version of CMake required to build the native library.

cmake_minimum_required(VERSION 3.4.1)

# AWS lib
set(path_to_common "${CMAKE_CURRENT_LIST_DIR}/../../../../..")
get_filename_component(path_to_common ${path_to_common} ABSOLUTE)

# This is required in order to append /lib/cmake to each element in CMAKE_PREFIX_PATH
set(AWS_MODULE_DIR "/${CMAKE_INSTALL_LIBDIR}/cmake")
string(REPLACE ";" "${AWS_MODULE_DIR};" AWS_MODULE_PATH "${CMAKE_PREFIX_PATH}${AWS_MODULE_DIR}")
# Append that generated list to the module search path
list(APPEND CMAKE_MODULE_PATH ${AWS_MODULE_PATH})

list(APPEND CMAKE_MODULE_PATH "${path_to_common}/cmake")
include(AwsFindPackage)
set(IN_SOURCE_BUILD ON)
set(BUILD_SHARED_LIBS ON)

# We will generate our own tests, the tests that are there depend on CTest
set(BUILD_TESTING OFF)
add_subdirectory(${path_to_common} ${CMAKE_CURRENT_BINARY_DIR}/aws-c-common)
aws_use_package(aws-c-common)

function(import_tests test_cmakelists)
    # Find all test cases in tests/CMakeLists.txt

    file(STRINGS ${test_cmakelists} test_case_lines REGEX "add_test_case.+")
    #message(STATUS "TEST_CASE_LINES=${test_case_lines}")
    foreach (line IN LISTS test_case_lines)
        string(STRIP "${line}" line)
        message(STATUS "LINE=${line}")
        string(REGEX REPLACE "add_test_case\\(([A-Za-z0-9_]+)\\)" "\\1" test_case "${line}")
        message(STATUS "TEST_CASE=${test_case}")
        list(APPEND TEST_CASES ${test_case})
    endforeach()

    if (ENABLE_NET_TESTS)
        file(STRINGS ${test_cmakelists} test_case_lines REGEX "add_net_test_case.+")
        #message(STATUS "TEST_CASE_LINES=${test_case_lines}")
        foreach (line IN LISTS test_case_lines)
            string(STRIP "${line}" line)
            message(STATUS "LINE=${line}")
            string(REGEX REPLACE "add_net_test_case\\(([A-Za-z0-9_]+)\\)" "\\1" test_case "${line}")
            message(STATUS "TEST_CASE=${test_case}")
            list(APPEND TEST_CASES ${test_case})
        endforeach()
    endif()

    # Generate Kotlin test classes
    get_filename_component(testrunner_path "../../androidTest/java/software/amazon/awssdk/crt/awscrtandroidtestrunner" ABSOLUTE)
    foreach(name IN LISTS TEST_CASES)
        set(TEST_NAME "${name}")
        #message(STATUS "TEST_NAME=${TEST_NAME}")
        configure_file(
            "${testrunner_path}/NativeTest.kt.in"
            "${testrunner_path}/tests/NativeTest_${name}.kt"
        )
    endforeach()
endfunction()

file(GLOB test_src "${path_to_common}/tests/*.c")
file(GLOB test_logging_src "${path_to_common}/tests/logging/*.c")
set(test_src ${test_src} ${test_logging_src})
import_tests(${path_to_common}/tests/CMakeLists.txt)

# JNI Lib
add_library(native-lib SHARED native-lib.cpp ${test_src})
find_library(log-lib log)
target_include_directories(native-lib PUBLIC
        "${path_to_common}/include"
        "${path_to_common}/tests"
        "${CMAKE_CURRENT_BINARY_DIR}/aws-c-common/generated/include")
target_compile_definitions(native-lib PRIVATE AWS_UNSTABLE_TESTING_API=1)
target_link_libraries(native-lib  ${log-lib} ${DEP_AWS_LIBS})