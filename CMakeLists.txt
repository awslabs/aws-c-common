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
option(ENABLE_HW_OPTIMIZATION "Enables hardware specific optimizations in assembly. Not all compilers are supported." ON)

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
    file(GLOB AWS_COMMON_OS_HEADERS
        "include/aws/common/posix/*"
        )
    file(GLOB AWS_COMMON_OS_SRC
        "source/posix/*.c"
        )
    if (APPLE)
        find_library(CORE_FOUNDATION_LIB CoreFoundation)
        if (NOT CORE_FOUNDATION_LIB)
            message(FATAL_ERROR "Core Foundation not found")
        endif ()

        set(PLATFORM_LIBS pthread ${CORE_FOUNDATION_LIB})
    elseif (${CMAKE_SYSTEM_NAME} STREQUAL "Linux") # Android does not link to libpthread nor librt, so this is fine
            set(PLATFORM_LIBS pthread rt)
    endif()
endif()

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

add_library(${CMAKE_PROJECT_NAME} ${COMMON_SRC})
aws_set_common_properties(${CMAKE_PROJECT_NAME} NO_WEXTRA)
#apple source already includes the definitions we want, and setting this posix source
#version causes it to revert to an older version. So don't turn it on there, we don't need it.
if (UNIX AND NOT APPLE)
    #this only gets applied to aws-c-common (not its consumers).
    target_compile_definitions(${CMAKE_PROJECT_NAME} PRIVATE -D_POSIX_C_SOURCE=200809L)
endif()

aws_add_sanitizers(${CMAKE_PROJECT_NAME} BLACKLIST "sanitizer-blacklist.txt")
target_link_libraries(${CMAKE_PROJECT_NAME} PUBLIC ${PLATFORM_LIBS})

# Our ABI is not yet stable
set_target_properties(${CMAKE_PROJECT_NAME} PROPERTIES SOVERSION 0unstable)

target_include_directories(${CMAKE_PROJECT_NAME} PUBLIC
        $<BUILD_INTERFACE:${CMAKE_CURRENT_SOURCE_DIR}/include>
        $<INSTALL_INTERFACE:include>)

# Enable SIMD encoder if the compiler supports the right features
simd_add_definitions(${CMAKE_PROJECT_NAME})

if (HAVE_MAY_I_USE OR HAVE_BUILTIN_CPU_SUPPORTS OR HAVE_MSVC_CPUIDEX)
    set(HAVE_SIMD_CPUID TRUE)
endif()

if (HAVE_AVX2_INTRINSICS AND HAVE_SIMD_CPUID)
    target_compile_definitions(${CMAKE_PROJECT_NAME} PRIVATE -DUSE_SIMD_ENCODING)
    target_sources(${CMAKE_PROJECT_NAME} PRIVATE "${CMAKE_CURRENT_SOURCE_DIR}/source/arch/cpuid.c")
    simd_add_source_avx2(${CMAKE_PROJECT_NAME} "${CMAKE_CURRENT_SOURCE_DIR}/source/arch/encoding_avx2.c")
    message(STATUS "Building SIMD base64 decoder")
endif()

if (ENABLE_HW_OPTIMIZATION)
    target_compile_definitions(${CMAKE_PROJECT_NAME} PRIVATE -DAWS_ENABLE_HW_OPTIMIZATION)
endif()

# Preserve subdirectories when installing headers
foreach(HEADER_SRCPATH IN ITEMS ${AWS_COMMON_HEADERS} ${AWS_COMMON_OS_HEADERS} ${AWS_TEST_HEADERS})
    get_filename_component(HEADER_DIR ${HEADER_SRCPATH} DIRECTORY)
    string(REPLACE ${CMAKE_CURRENT_SOURCE_DIR} ${CMAKE_INSTALL_PREFIX} HEADER_DSTDIR "${HEADER_DIR}")
    install(FILES ${HEADER_SRCPATH} DESTINATION ${HEADER_DSTDIR})
endforeach()

set(LIBRARY_DIRECTORY ${CMAKE_INSTALL_PREFIX}/lib)

install(TARGETS ${CMAKE_PROJECT_NAME}
    EXPORT ${CMAKE_PROJECT_NAME}-targets
    ARCHIVE DESTINATION ${LIBRARY_DIRECTORY}
    LIBRARY DESTINATION ${LIBRARY_DIRECTORY}
    RUNTIME DESTINATION ${LIBRARY_DIRECTORY})

configure_file("cmake/${CMAKE_PROJECT_NAME}-config.cmake"
  "${CMAKE_CURRENT_BINARY_DIR}/${CMAKE_PROJECT_NAME}-config.cmake"
  @ONLY)

install(EXPORT "${CMAKE_PROJECT_NAME}-targets"
    DESTINATION "${LIBRARY_DIRECTORY}/${CMAKE_PROJECT_NAME}/cmake/"
    NAMESPACE AWS::)

install(FILES "${CMAKE_CURRENT_BINARY_DIR}/${CMAKE_PROJECT_NAME}-config.cmake"
    DESTINATION "${LIBRARY_DIRECTORY}/${CMAKE_PROJECT_NAME}/cmake/")

list(APPEND EXPORT_MODULES
    "cmake/AwsCFlags.cmake"
    "cmake/AwsTestHarness.cmake"
    "cmake/LibFuzzer.cmake"
    "cmake/Sanitizers.cmake"
    "cmake/SIMD.cmake"
    )

install(FILES ${EXPORT_MODULES} DESTINATION "lib/cmake/")

if (NOT CMAKE_CROSSCOMPILING)
    include(CTest)
    add_subdirectory(tests)
endif()
