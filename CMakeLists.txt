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

file(GLOB AWS_COMMON_HEADERS
        "include/aws/common/*.h"
        )

file(GLOB AWS_TEST_HEADERS
        "include/aws/testing/*.h"
        )

file(GLOB AWS_COMMON_PRIV_HEADERS
        "include/aws/common/private/*.h"
        "include/aws/common/private/*.c"
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
        source_group("Header Files\\aws\\testing" FILES ${AWS_TEST_HEADERS})
        source_group("Source Files" FILES ${AWS_COMMON_SRC})
        source_group("Source Files\\windows" FILES ${AWS_COMMON_OS_SRC})
    endif ()

    set(PLATFORM_LIBS Kernel32 Ws2_32)
else ()
    if (${CMAKE_SYSTEM_NAME} STREQUAL "Linux" OR (UNIX AND NOT APPLE))
        file(GLOB AWS_COMMON_OS_SRC
                "source/posix/*.c"
                )
        set(PLATFORM_LIBS pthread rt)
    elseif (APPLE)
        file(GLOB AWS_COMMON_OS_SRC
                "source/posix/*.c"
                )

        find_library(CORE_FOUNDATION_LIB CoreFoundation)
        if (NOT CORE_FOUNDATION_LIB)
            message(FATAL_ERROR "Core Foundation not founc")
        endif ()

        set(PLATFORM_LIBS pthread ${CORE_FOUNDATION_LIB})
    endif ()
endif ()

file(GLOB COMMON_HEADERS
        ${AWS_COMMON_HEADERS}
        ${AWS_COMMON_PRIV_HEADERS}
        ${AWS_TEST_HEADERS}
        )

file(GLOB COMMON_SRC
        ${AWS_COMMON_SRC}
        ${AWS_COMMON_OS_SRC}
        )

if (BUILD_SHARED_LIBS)
    if (WIN32)
        add_definitions("-DUSE_IMPORT_EXPORT")
    endif ()
endif ()

add_library(${CMAKE_PROJECT_NAME} ${LIBTYPE} ${COMMON_SRC})
set_target_properties(${CMAKE_PROJECT_NAME} PROPERTIES LINKER_LANGUAGE C C_STANDARD 99)

if (MSVC)
    target_compile_options(${CMAKE_PROJECT_NAME} PRIVATE /W4 /WX)
else ()
    target_compile_options(${CMAKE_PROJECT_NAME} PRIVATE -Wall -pedantic -Werror -Wno-long-long)
endif ()

if (BUILD_SHARED_LIBS AND WIN32)
    target_compile_definitions(${CMAKE_PROJECT_NAME} PRIVATE "-DAWS_COMMON_EXPORTS")
endif ()

if (CMAKE_BUILD_TYPE STREQUAL "" OR CMAKE_BUILD_TYPE MATCHES Debug)
    target_compile_definitions(${CMAKE_PROJECT_NAME} PRIVATE "-DDEBUG_BUILD")
endif ()

target_include_directories(${CMAKE_PROJECT_NAME} PUBLIC
        $<BUILD_INTERFACE:${CMAKE_CURRENT_SOURCE_DIR}/include>
        $<INSTALL_INTERFACE:include>)

target_link_libraries(${CMAKE_PROJECT_NAME} ${PLATFORM_LIBS})

install(FILES ${AWS_COMMON_HEADERS} DESTINATION "${CMAKE_INSTALL_PREFIX}/include/aws/common")
install(FILES ${AWS_TEST_HEADERS} DESTINATION "${CMAKE_INSTALL_PREFIX}/include/aws/testing")

install(
    TARGETS ${CMAKE_PROJECT_NAME} EXPORT ${CMAKE_PROJECT_NAME}-config
        ARCHIVE DESTINATION ${CMAKE_INSTALL_PREFIX}/lib
        LIBRARY DESTINATION ${CMAKE_INSTALL_PREFIX}/lib
        COMPONENT library
)

export(TARGETS ${CMAKE_PROJECT_NAME} FILE ${CMAKE_PROJECT_NAME}-config.cmake)
install(EXPORT ${CMAKE_PROJECT_NAME}-config DESTINATION "${CMAKE_INSTALL_PREFIX}/lib/${CMAKE_PROJECT_NAME}/cmake/")

include(CTest)
add_subdirectory(tests)
