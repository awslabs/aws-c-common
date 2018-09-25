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
project(aws-c-common C)

list(APPEND CMAKE_MODULE_PATH "${CMAKE_CURRENT_SOURCE_DIR}/cmake")
include(AwsCFlags)
include(Sanitizers)
include(SIMD)

file(GLOB AWS_COMMON_HEADERS
        "include/aws/common/*.h"
        "include/aws/common/*.inl"
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

option(PERFORM_HEADER_CHECK "Performs compile-time checks that each header can be included independently. Requires a C++ compiler.")

if (WIN32)
    file(GLOB AWS_COMMON_OS_HEADERS
            "include/aws/common/windows/*"
            )
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
        file(GLOB AWS_COMMON_OS_HEADERS
                "include/aws/common/posix/*"
                )
        file(GLOB AWS_COMMON_OS_SRC
                "source/posix/*.c"
                )
        set(PLATFORM_LIBS pthread rt)
    elseif (APPLE)
        file(GLOB AWS_COMMON_OS_HEADERS
                "include/aws/common/posix/*"
                )
        file(GLOB AWS_COMMON_OS_SRC
                "source/posix/*.c"
                )

        find_library(CORE_FOUNDATION_LIB CoreFoundation)
        if (NOT CORE_FOUNDATION_LIB)
            message(FATAL_ERROR "Core Foundation not found")
        endif ()

        set(PLATFORM_LIBS pthread ${CORE_FOUNDATION_LIB})
    endif ()
endif ()

file(GLOB COMMON_HEADERS
        ${AWS_COMMON_HEADERS}
        ${AWS_COMMON_OS_HEADERS}
        ${AWS_COMMON_PRIV_HEADERS}
        ${AWS_TEST_HEADERS}
        )

file(GLOB COMMON_SRC
        ${AWS_COMMON_SRC}
        ${AWS_COMMON_OS_SRC}
        )

if (PERFORM_HEADER_CHECK)
    set(HEADERS_TO_CHECK ${AWS_COMMON_HEADERS} ${AWS_TEST_HEADERS} ${AWS_COMMON_OS_HEADERS})
    add_subdirectory(cmake/header-tester)
endif()

add_library(${CMAKE_PROJECT_NAME} ${LIBTYPE} ${COMMON_SRC})
aws_set_common_properties(${CMAKE_PROJECT_NAME} NO_WEXTRA)
if (UNIX AND NOT APPLE)
    #this only gets applied to aws-c-common (not its consumers).
    target_compile_definitions(${CMAKE_PROJECT_NAME} PRIVATE -D_POSIX_C_SOURCE=200809L)
endif()

aws_add_sanitizers(${CMAKE_PROJECT_NAME} BLACKLIST "sanitizer-blacklist.txt")
target_link_libraries(${CMAKE_PROJECT_NAME} PUBLIC ${PLATFORM_LIBS})

target_include_directories(${CMAKE_PROJECT_NAME} PUBLIC
        $<BUILD_INTERFACE:${CMAKE_CURRENT_SOURCE_DIR}/include>
        $<INSTALL_INTERFACE:include>)

# Enable SIMD encoder if the compiler supports the right features
simd_add_definitions(${CMAKE_PROJECT_NAME})

if (HAVE_MAY_I_USE OR HAVE_BUILTIN_CPU_SUPPORTS OR HAVE_MSVC_CPUIDEX)
    set(HAVE_SIMD_CPUID TRUE)
    target_sources(${CMAKE_PROJECT_NAME} PRIVATE "${CMAKE_CURRENT_SOURCE_DIR}/source/arch/cpuid.c")
endif()

if (HAVE_AVX2_INTRINSICS AND HAVE_SIMD_CPUID)
	target_compile_definitions(${CMAKE_PROJECT_NAME} PRIVATE -DUSE_SIMD_ENCODING)
    simd_add_source_avx2(${CMAKE_PROJECT_NAME} "${CMAKE_CURRENT_SOURCE_DIR}/source/arch/encoding_avx2.c")
endif()

# Preserve subdirectories when installing headers
foreach(HEADER_SRCPATH IN ITEMS ${AWS_COMMON_HEADERS} ${AWS_COMMON_OS_HEADERS} ${AWS_TEST_HEADERS})
    get_filename_component(HEADER_DIR ${HEADER_SRCPATH} DIRECTORY)
    string(REPLACE ${CMAKE_CURRENT_SOURCE_DIR} ${CMAKE_INSTALL_PREFIX} HEADER_DSTDIR "${HEADER_DIR}")
    install(FILES ${HEADER_SRCPATH} DESTINATION ${HEADER_DSTDIR})
endforeach()

install(
    TARGETS ${CMAKE_PROJECT_NAME} EXPORT ${CMAKE_PROJECT_NAME}-config
        ARCHIVE DESTINATION ${CMAKE_INSTALL_PREFIX}/lib
        LIBRARY DESTINATION ${CMAKE_INSTALL_PREFIX}/lib
        COMPONENT library
)

export(TARGETS ${CMAKE_PROJECT_NAME} FILE ${CMAKE_PROJECT_NAME}-config.cmake)
install(EXPORT ${CMAKE_PROJECT_NAME}-config DESTINATION "lib/${CMAKE_PROJECT_NAME}/cmake/")

file(GLOB EXPORT_MODULES "cmake/*.cmake")
install(FILES ${EXPORT_MODULES} DESTINATION "lib/cmake/")

include(CTest)
add_subdirectory(tests)
