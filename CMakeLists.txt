# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0.

cmake_minimum_required(VERSION 3.0)
option(ALLOW_CROSS_COMPILED_TESTS "Allow tests to be compiled via cross compile, for use with qemu" OFF)

project(aws-c-common LANGUAGES C VERSION 0.1.0)

message(STATUS "CMake ${CMAKE_VERSION}")

if (POLICY CMP0069)
    cmake_policy(SET CMP0069 NEW) # Enable LTO/IPO if available in the compiler, see AwsCFlags
endif()

if (POLICY CMP0077)
    cmake_policy(SET CMP0077 OLD) # Enable options to get their values from normal variables
endif()

list(APPEND CMAKE_MODULE_PATH "${CMAKE_CURRENT_SOURCE_DIR}/cmake")
include(AwsCFlags)
include(AwsCheckHeaders)
include(AwsSharedLibSetup)
include(AwsFeatureTests)
include(AwsSanitizers)
include(AwsThreadAffinity)
include(AwsThreadName)
include(AwsSIMD)
include(CTest)

set(GENERATED_ROOT_DIR "${CMAKE_CURRENT_BINARY_DIR}/generated")
set(GENERATED_INCLUDE_DIR "${GENERATED_ROOT_DIR}/include")
set(GENERATED_CONFIG_HEADER "${GENERATED_INCLUDE_DIR}/aws/common/config.h")
set(CONFIG_HEADER_TEMPLATE "${CMAKE_CURRENT_SOURCE_DIR}/include/aws/common/config.h.in")

file(GLOB AWS_COMMON_HEADERS
        "include/aws/common/*.h"
        "include/aws/common/*.inl"
        )

file (GLOB AWS_COMMON_EXTERNAL_HEADERS
        "include/aws/common/external/*.h")

file (GLOB AWS_COMMON_EXTERNAL_INSTALLED_HEADERS
        "include/aws/common/external/ittnotify.h")

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

file (GLOB AWS_COMMON_EXTERNAL_SRC
        "source/external/*.c")

option(AWS_NUM_CPU_CORES "Number of CPU cores of the target machine. Useful when cross-compiling." 0)

if (WIN32)
    set(WINDOWS_KERNEL_LIB "Kernel32" CACHE STRING "The name of the kernel library to link against (default: Kernel32)")

    file(GLOB AWS_COMMON_OS_HEADERS
        "include/aws/common/windows/*"
        )

    file(GLOB AWS_COMMON_OS_SRC
        "source/windows/*.c"
        "source/platform_fallback_stubs/system_info.c"
        )

    if (MSVC)
        source_group("Header Files\\aws\\common" FILES ${AWS_COMMON_HEADERS})
        source_group("Header Files\\aws\\common\\private" FILES ${AWS_COMMON_PRIV_HEADERS})
        source_group("Header Files\\aws\\testing" FILES ${AWS_TEST_HEADERS})
        source_group("Source Files" FILES ${AWS_COMMON_SRC})
        source_group("Source Files\\windows" FILES ${AWS_COMMON_OS_SRC})
    endif ()

    list(APPEND PLATFORM_DEFINES WINDOWS_KERNEL_LIB=${WINDOWS_KERNEL_LIB})
    # PSAPI_VERSION=1 is needed to support GetProcessMemoryInfo on both pre and
    # post Win7 OS's. 
    list(APPEND PLATFORM_DEFINES PSAPI_VERSION=1)
    list(APPEND PLATFORM_LIBS BCrypt ${WINDOWS_KERNEL_LIB} Ws2_32 Shlwapi Psapi)
else ()
    file(GLOB AWS_COMMON_OS_HEADERS
        "include/aws/common/posix/*"
        )
    file(GLOB AWS_COMMON_OS_SRC
        "source/posix/*.c"
        )

    set(THREADS_PREFER_PTHREAD_FLAG ON)

    if (UNIX OR APPLE)
        find_package(Threads REQUIRED)

        if (NOT ANDROID AND NOT CMAKE_THREAD_LIBS_INIT)
            check_symbol_exists(pthread_mutexattr_init "<pthread.h>" HAVE_PTHREAD_MUTEXATTR_INIT)
            if (NOT HAVE_PTHREAD_MUTEXATTR_INIT)
                # fsanitize=... results in GLIBC library to provide some pthread APIs but not all
                list(APPEND PLATFORM_LIBS pthread)
            endif()
        endif()
    endif()

    if (APPLE)
        # Don't add the exact path to CoreFoundation as this would hardcode the SDK version
        list(APPEND PLATFORM_LIBS dl Threads::Threads "-framework CoreFoundation")
        list (APPEND AWS_COMMON_OS_SRC "source/darwin/*.c") # OS specific includes
        list (APPEND AWS_COMMON_OS_SRC "source/platform_fallback_stubs/system_info.c")
    elseif (${CMAKE_SYSTEM_NAME} STREQUAL "Linux") # Android does not link to libpthread nor librt, so this is fine
        list(APPEND PLATFORM_LIBS dl m Threads::Threads rt)
        list (APPEND AWS_COMMON_OS_SRC "source/linux/*.c") # OS specific includes
    elseif(CMAKE_SYSTEM_NAME STREQUAL "FreeBSD")
        list(APPEND PLATFORM_LIBS dl m thr execinfo)
        list (APPEND AWS_COMMON_OS_SRC "source/platform_fallback_stubs/system_info.c")
    elseif(CMAKE_SYSTEM_NAME STREQUAL "NetBSD")
        list(APPEND PLATFORM_LIBS dl m Threads::Threads execinfo)
        list (APPEND AWS_COMMON_OS_SRC "source/platform_fallback_stubs/system_info.c")
    elseif(CMAKE_SYSTEM_NAME STREQUAL "OpenBSD")
        list(APPEND PLATFORM_LIBS m Threads::Threads execinfo)
        list (APPEND AWS_COMMON_OS_SRC "source/platform_fallback_stubs/system_info.c")
    elseif(CMAKE_SYSTEM_NAME STREQUAL "Android")
        list(APPEND PLATFORM_LIBS log)
        file(GLOB ANDROID_SRC "source/android/*.c")
        list(APPEND AWS_COMMON_OS_SRC "${ANDROID_SRC}")
        list (APPEND AWS_COMMON_OS_SRC "source/platform_fallback_stubs/system_info.c")
    else()
        list (APPEND AWS_COMMON_OS_SRC "source/platform_fallback_stubs/system_info.c")
    endif()

endif()

file(GLOB AWS_COMMON_ARCH_SRC
     "source/arch/generic/*.c"
     )

if (USE_CPU_EXTENSIONS)
    if (AWS_ARCH_INTEL)
        if (MSVC)
            file(GLOB AWS_COMMON_ARCH_SRC
                "source/arch/intel/cpuid.c"
                "source/arch/intel/msvc/*.c"
                )

            source_group("Source Files\\arch\\intel" FILES ${AWS_COMMON_ARCH_SRC})
        else()
            file(GLOB AWS_COMMON_ARCH_SRC
                "source/arch/intel/cpuid.c"
                "source/arch/intel/asm/*.c"
                )
        endif()
    elseif (AWS_ARCH_ARM64 OR AWS_ARCH_ARM32)
        if (MSVC)
            file(GLOB AWS_COMMON_ARCH_SRC
                "source/arch/arm/msvc/*.c"
                )
        elseif (AWS_HAVE_AUXV)
            file(GLOB AWS_COMMON_ARCH_SRC
                "source/arch/arm/asm/*.c"
                )
        endif()
    endif()
endif()

list(APPEND PLATFORM_LIBS ${CMAKE_DL_LIBS})

file(GLOB COMMON_HEADERS
        ${AWS_COMMON_HEADERS}
        ${AWS_COMMON_OS_HEADERS}
        ${AWS_COMMON_PRIV_HEADERS}
        ${AWS_COMMON_EXTERNAL_HEADERS}
        ${AWS_TEST_HEADERS}
        )

file(GLOB COMMON_SRC
        ${AWS_COMMON_SRC}
        ${AWS_COMMON_OS_SRC}
        ${AWS_COMMON_ARCH_SRC}
        ${AWS_COMMON_EXTERNAL_SRC}
        )


add_library(${PROJECT_NAME} ${COMMON_SRC})
aws_set_common_properties(${PROJECT_NAME} NO_WEXTRA)
aws_prepare_symbol_visibility_args(${PROJECT_NAME} "AWS_COMMON")
target_compile_options(${PROJECT_NAME} PUBLIC ${PLATFORM_CFLAGS})

aws_check_headers(${PROJECT_NAME} ${AWS_COMMON_HEADERS})

#apple source already includes the definitions we want, and setting this posix source
#version causes it to revert to an older version. So don't turn it on there, we don't need it.
if (UNIX AND NOT APPLE AND NOT ${CMAKE_SYSTEM_NAME} MATCHES FreeBSD|OpenBSD)
    #this only gets applied to aws-c-common (not its consumers).
    target_compile_definitions(${PROJECT_NAME} PRIVATE -D_POSIX_C_SOURCE=200809L -D_XOPEN_SOURCE=500)
endif()

aws_set_thread_affinity_method(${PROJECT_NAME})
aws_set_thread_name_method(${PROJECT_NAME})

aws_add_sanitizers(${PROJECT_NAME})
target_link_libraries(${PROJECT_NAME} PUBLIC ${PLATFORM_LIBS})
target_compile_definitions(${PROJECT_NAME} PRIVATE ${PLATFORM_DEFINES})

if (AWS_NUM_CPU_CORES)
    target_compile_definitions(${PROJECT_NAME} PRIVATE -DAWS_NUM_CPU_CORES=${AWS_NUM_CPU_CORES})
endif()

set_target_properties(${PROJECT_NAME} PROPERTIES VERSION 1.0.0)
set_target_properties(${PROJECT_NAME} PROPERTIES SOVERSION 1)

target_include_directories(${PROJECT_NAME} PUBLIC
        $<BUILD_INTERFACE:${CMAKE_CURRENT_SOURCE_DIR}/include>
        $<INSTALL_INTERFACE:include>)
# When we install, the generated header will be at the INSTALL_INTERFACE:include location,
# but at build time we need to explicitly include this here
target_include_directories(${PROJECT_NAME} PUBLIC
        $<BUILD_INTERFACE:${GENERATED_INCLUDE_DIR}>)

target_compile_definitions(${PROJECT_NAME} PRIVATE -DCJSON_HIDE_SYMBOLS)

# Enable SIMD encoder if the compiler supports the right features
simd_add_definitions(${PROJECT_NAME})

if (HAVE_AVX2_INTRINSICS)
    target_compile_definitions(${PROJECT_NAME} PRIVATE -DUSE_SIMD_ENCODING)
    simd_add_source_avx2(${PROJECT_NAME} "source/arch/intel/encoding_avx2.c")
    message(STATUS "Building SIMD base64 decoder")
endif()

# Preserve subdirectories when installing headers
foreach(HEADER_SRCPATH IN ITEMS ${AWS_COMMON_HEADERS} ${AWS_COMMON_OS_HEADERS} ${GENERATED_CONFIG_HEADER} ${AWS_TEST_HEADERS} ${AWS_COMMON_EXTERNAL_INSTALLED_HEADERS})
    get_filename_component(HEADER_DIR ${HEADER_SRCPATH} DIRECTORY)
# Note: We need to replace the generated include directory component first, otherwise if the build
# directory is located inside the source tree, we'll partially rewrite the path and fail to replace it
# when we replace the generated include dir.
# We also need to take care to not run the source-directory match if the generated-directory match
# succeeds; otherwise, if we're installing to /foo/aws-c-common-install, and our source directory is
# /foo/aws-c-common, we'll end up installing to /foo/aws-c-common-install-install

    unset(HEADER_DSTDIR)

    foreach(POTENTIAL_PREFIX IN ITEMS ${GENERATED_ROOT_DIR} ${CMAKE_CURRENT_SOURCE_DIR})
        string(LENGTH ${POTENTIAL_PREFIX} _prefixlen)
        string(SUBSTRING ${HEADER_DIR} 0 ${_prefixlen} _actual_prefix)
        if(${_actual_prefix} STREQUAL ${POTENTIAL_PREFIX})
            string(REPLACE "${POTENTIAL_PREFIX}/" "" HEADER_DSTDIR "${HEADER_DIR}")
            break()
        endif()
    endforeach()

    if(NOT HEADER_DSTDIR)
        message(ERROR "Couldn't find source root for header ${HEADER_SRCPATH}")
    endif()

    install(FILES ${HEADER_SRCPATH}
            DESTINATION ${HEADER_DSTDIR}
            COMPONENT Development)
endforeach()

aws_prepare_shared_lib_exports(${PROJECT_NAME})

configure_file("cmake/${PROJECT_NAME}-config.cmake"
  "${CMAKE_CURRENT_BINARY_DIR}/${PROJECT_NAME}-config.cmake"
  @ONLY)

if (BUILD_SHARED_LIBS)
   set (TARGET_DIR "shared")
else()
   set (TARGET_DIR "static")
endif()

install(EXPORT "${PROJECT_NAME}-targets"
    DESTINATION "${LIBRARY_DIRECTORY}/${PROJECT_NAME}/cmake/${TARGET_DIR}"
    NAMESPACE AWS::
    COMPONENT Development)

install(FILES "${CMAKE_CURRENT_BINARY_DIR}/${PROJECT_NAME}-config.cmake"
    DESTINATION "${LIBRARY_DIRECTORY}/${PROJECT_NAME}/cmake"
    COMPONENT Development)

list(APPEND EXPORT_MODULES
    "cmake/AwsCFlags.cmake"
    "cmake/AwsCheckHeaders.cmake"
    "cmake/AwsSharedLibSetup.cmake"
    "cmake/AwsTestHarness.cmake"
    "cmake/AwsLibFuzzer.cmake"
    "cmake/AwsSanitizers.cmake"
    "cmake/AwsSIMD.cmake"
    "cmake/AwsFindPackage.cmake"
    "cmake/AwsFeatureTests.cmake"
    "cmake/AwsCRuntime.cmake"
    )

install(FILES ${EXPORT_MODULES}
        DESTINATION "${LIBRARY_DIRECTORY}/cmake"
        COMPONENT Development)

# This should come last, to ensure all variables defined by cmake will be available for export
configure_file(${CONFIG_HEADER_TEMPLATE}
        ${GENERATED_CONFIG_HEADER}
        ESCAPE_QUOTES)

if (ALLOW_CROSS_COMPILED_TESTS OR NOT CMAKE_CROSSCOMPILING)
    if (BUILD_TESTING)
        add_subdirectory(tests)
        add_subdirectory(bin/system_info)
    endif()
endif()

include(CPackConfig)
