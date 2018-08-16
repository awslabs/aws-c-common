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

include(CheckCCompilerFlag)
include(CheckIncludeFile)

check_include_file(immintrin.h HAS_IMMINTRIN)
check_include_file(emmintrin.h HAS_EMMINTRIN)

check_c_compiler_flag(-msse4.1 HAVE_M_SSE41)
check_c_compiler_flag(-mavx2 HAVE_M_AVX2)

if (HAS_IMMINTRIN AND HAS_EMMINTRIN)
# Do we need to pass compiler flags to enable SSE stuff?
    if (HAVE_M_SSE41 AND HAVE_M_AVX2)
        set(SSE41_CFLAGS "-mavx -mavx2 -mssse3 -msse4 -msse4.1")
    endif()

    set(old_flags "${CMAKE_REQUIRED_FLAGS}")
    set(CMAKE_REQUIRED_FLAGS "${CMAKE_REQUIRED_FLAGS} ${SSE41_CFLAGS}")

    check_c_source_compiles("
#include <immintrin.h>
#include <emmintrin.h>
#include <string.h>

int main() {
    __m256i vec;
    memset(&vec, 0, sizeof(vec));

    _mm256_shuffle_epi8(vec, vec);
    _mm256_set_epi32(1,2,3,4,5,6,7,8);
    _mm256_permutevar8x32_epi32(vec, vec);

    return 0;
}"  USE_SIMD_ENCODING)

    check_c_source_compiles("
#include <immintrin.h>

int main() {
    return _may_i_use_cpu_feature(_FEATURE_AVX2 | _FEATURE_SSE4_1);
}
"   USE_MAY_I_USE)

    check_c_source_compiles("
#include <immintrin.h>

int main() {
    return __builtin_cpu_supports(\"sse4.1\");
}
"   USE_BUILTIN_CPU_SUPPORTS)
    set(CMAKE_REQUIRED_FLAGS "${old_flags}")

    if (USE_MAY_I_USE)
        add_definitions(-DUSE_MAY_I_USE)
    elseif(USE_BUILTIN_CPU_SUPPORTS)
        add_definitions(-DUSE_BUILTIN_CPU_SUPPORTS)
    else()
        set(USE_SIMD_ENCODING FALSE)
    endif()

    if (USE_SIMD_ENCODING)
        set(encoding_simd_source ${CMAKE_CURRENT_SOURCE_DIR}/source/arch/encoding_simd_sse41.c)
        target_sources(${CMAKE_PROJECT_NAME} PRIVATE ${encoding_simd_source})
        set_source_files_properties(${encoding_simd_source} COMPILE_FLAGS "${SSE41_CFLAGS}")
        add_definitions(-DUSE_SIMD_ENCODING)
    endif()
endif()
