# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0.

include(CheckCCompilerFlag)
include(CheckIncludeFile)

if (MSVC)
    set(AWS_AVX2_FLAG "/arch:AVX2")
    set(AWS_AVX512_FLAG "/arch:AVX512")
    set(AWS_AVX512vL_FLAG "")
    set(AWS_PCMUL_FLAG "")
    set(AWS_SSE4_2_FLAG "")
else()
    set(AWS_AVX2_FLAG "-mavx -mavx2")
    set(AWS_AVX512_FLAG "-mavx512f")
    set(AWS_AVX512vL_FLAG "mavx512vl")
    set(AWS_PCMUL_FLAG "-mvpclmulqdq -mpcmul")
    set(AWS_SSE4_2_FLAG "-msse4.2")
endif()

if (USE_CPU_EXTENSIONS)
    check_c_compiler_flag(${AWS_AVX2_FLAG} HAVE_M_AVX2_FLAG)
    if (HAVE_M_AVX2_FLAG)
        set(AVX_CFLAGS ${AWS_AVX2_FLAG})
    endif()

    check_c_compiler_flag("${AWS_AVX512_FLAG} ${AWS_PCMUL_FLAG}" HAVE_M_AVX512_FLAG)
    if (HAVE_M_AVX512_FLAG)
        set(AVX_CFLAGS "${AVX_CFLAGS} ${AWS_AVX512_FLAG} ${AWS_PCMUL_FLAG} ${AWS_SSE4_2_FLAG}")
    endif()

    set(old_flags "${CMAKE_REQUIRED_FLAGS}")
    set(CMAKE_REQUIRED_FLAGS "${CMAKE_REQUIRED_FLAGS} ${AVX_CFLAGS}")

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
        }"  AWS_HAVE_AVX2_INTRINSICS)          

    check_c_source_compiles("
        #include <immintrin.h>

        int main() {
            __m512 a = _mm512_setzero_ps();
            return 0;
        }" AWS_HAVE_AVX512_INTRINSICS)

    check_c_source_compiles("
        #include <immintrin.h>
        #include <string.h>

        int main() {
            __m256i vec;
            memset(&vec, 0, sizeof(vec));
            return (int)_mm256_extract_epi64(vec, 2);
        }" AWS_HAVE_MM256_EXTRACT_EPI64)

    set(CMAKE_REQUIRED_FLAGS "${old_flags}")
endif() # USE_CPU_EXTENSIONS

# The part where the definition is added to the compiler flags has been moved to config.h.in
# see git history for more details.

# Adds AVX flags, if any, that are supported. These files will be built with
# available avx intrinsics enabled.
# Usage: simd_add_source_avx(target file1.c file2.c ...)
function(simd_add_source_avx target)
    foreach(file ${ARGN})
        target_sources(${target} PRIVATE ${file})
        set_source_files_properties(${file} PROPERTIES COMPILE_FLAGS "${AVX_CFLAGS}")
    endforeach()
endfunction(simd_add_source_avx)


function(simd_append_source_avx512 target)
    foreach(file ${ARGN})
        target_sources(${target} PRIVATE ${file})
        set_property(${file} APPEND PROPERTY COMPILE_OPTIONS "${AWS_AVX512_FLAG}")
    endforeach()
endfunction(simd_append_source_avx512)

function(simd_append_source_avx2 target)
    foreach(file ${ARGN})
        target_sources(${target} PRIVATE ${file})
        set_property(${file} APPEND PROPERTY COMPILE_OPTIONS "${AWS_AVX2_FLAG}")
    endforeach()
endfunction(simd_append_source_avx2)

function(simd_append_source_avx512vl target)
    foreach(file ${ARGN})
        target_sources(${target} PRIVATE ${file})
        set_property(${file} APPEND PROPERTY COMPILE_OPTIONS "${AWS_AVX512vl_FLAG}")
    endforeach()
endfunction(simd_append_source_avx512vl)

function(simd_append_source_pcmul target)
    foreach(file ${ARGN})
        target_sources(${target} PRIVATE ${file})
        set_property(${file} APPEND PROPERTY COMPILE_OPTIONS "${AWS_PCMUL_FLAG}")
    endforeach()
endfunction(simd_append_source_pcmul)

function(simd_append_source_sse42 target)
    foreach(file ${ARGN})
        target_sources(${target} PRIVATE ${file})
        set_property(${file} APPEND PROPERTY COMPILE_OPTIONS "${AWS_SSE4_2_FLAG}")
    endforeach()
endfunction(simd_append_source_sse42)
