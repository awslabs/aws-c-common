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

cmake_minimum_required(VERSION 3.0)
project(aws-c-common)

set(PROJECT_NAME aws-c-common)

file(GLOB AWS_COMMON_HEADERS
        "include/aws/common/*.h"
        )

file(GLOB AWS_COMMON_PRIV_HEADERS
        "include/aws/common/private/*.h"
        )

file(GLOB AWS_COMMON_SRC
        "source/*.c"
        )

if (WIN32)
    file(GLOB AWS_COMMON_OS_SRC
            "source/windows/*.c"
            )

    if (MSVC)
        source_group("Header Files\\aws\\common" FILES ${AWS_COMMON_HEADERS})
        source_group("Header Files\\aws\\common\\private" FILES ${AWS_COMMON_PRIV_HEADERS})
        source_group("Source Files" FILES ${AWS_COMMON_SRC})
        source_group("Source Files\\windows" FILES ${AWS_COMMON_OS_SRC})
    endif ()

    set(PLATFORM_LIBS "Kernel32")
else ()
    file(GLOB AWS_COMMON_OS_SRC
            "source/posix/*.c"
            )

    set(PLATFORM_LIBS "pthread" "rt")
endif ()

file(GLOB COMMON_HEADERS
        ${AWS_COMMON_HEADERS}
        ${AWS_COMMON_PRIV_HEADERS}
        )

file(GLOB COMMON_SRC
        ${AWS_COMMON_SRC}
        ${AWS_COMMON_OS_SRC}
        )

if (BUILD_SHARED_LIBS)
    set(LIBTYPE SHARED)
    if (WIN32)
        add_definitions("-DUSE_IMPORT_EXPORT")
    endif ()
else ()
    set(LIBTYPE STATIC)
endif ()

add_library(aws-c-common ${LIBTYPE} ${COMMON_HEADERS} ${COMMON_SRC})
set_target_properties(aws-c-common PROPERTIES LINKER_LANGUAGE C C_STANDARD 99)
set(CMAKE_C_FLAGS_DEBUGOPT "")

#set warnings
if (MSVC)
    target_compile_options(aws-c-common PRIVATE /W4)
else ()
    target_compile_options(aws-c-common PRIVATE -Wall -Wno-long-long -pedantic -Werror)
endif ()

if (BUILD_SHARED_LIBS AND WIN32)
    target_compile_definitions(aws-c-common PRIVATE "-DAWS_COMMON_EXPORTS")
endif ()

if (CMAKE_BUILD_TYPE STREQUAL "" OR CMAKE_BUILD_TYPE MATCHES DEBUG)
    target_compile_definitions(aws-c-common PRIVATE "-DDEBUG_BUILD")
endif ()

target_include_directories(aws-c-common PUBLIC
        $<BUILD_INTERFACE:${CMAKE_CURRENT_SOURCE_DIR}/include>
        $<INSTALL_INTERFACE:include>)

target_link_libraries(aws-c-common ${PLATFORM_LIBS})

file(GLOB TEST_SRC "tests/*.c")
file(GLOB TEST_HDRS "tests/*.h")
file(GLOB TESTS ${TEST_HDRS} ${TEST_SRC})

include_directories(${CMAKE_CURRENT_SOURCE_DIR}/tests)
add_executable(aws-c-common-tests ${TESTS})
target_link_libraries(aws-c-common-tests aws-c-common)
set_target_properties(aws-c-common-tests PROPERTIES LINKER_LANGUAGE C C_STANDARD 99)

include(CTest)
enable_testing()

add_test(raise_errors_test aws-c-common-tests raise_errors_test)
add_test(reset_errors_test aws-c-common-tests reset_errors_test)
add_test(error_callback_test aws-c-common-tests error_callback_test)
add_test(unknown_error_code_in_slot_test aws-c-common-tests unknown_error_code_in_slot_test)
add_test(unknown_error_code_no_slot_test aws-c-common-tests unknown_error_code_no_slot_test)
add_test(unknown_error_code_range_too_large_test aws-c-common-tests unknown_error_code_range_too_large_test)

install(FILES ${AWS_COMMON_HEADERS} DESTINATION "${CMAKE_INSTALL_PREFIX}/include/aws/common")
install(
        TARGETS aws-c-common EXPORT aws-c-common-config
        ARCHIVE DESTINATION ${CMAKE_INSTALL_PREFIX}/lib
        LIBRARY DESTINATION ${CMAKE_INSTALL_PREFIX}/lib
        COMPONENT library
)

export(TARGETS aws-c-common FILE aws-c-common-config.cmake)
install(EXPORT aws-c-common-config DESTINATION "${CMAKE_INSTALL_PREFIX}/lib/aws-c-common/cmake/")

