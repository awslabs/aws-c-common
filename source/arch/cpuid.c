/*
 * Copyright 2010-2018 Amazon.com, Inc. or its affiliates. All Rights Reserved.
 *
 * Licensed under the Apache License, Version 2.0 (the "License").
 * You may not use this file except in compliance with the License.
 * A copy of the License is located at
 *
 *  http://aws.amazon.com/apache2.0
 *
 * or in the "license" file accompanying this file. This file is distributed
 * on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 * express or implied. See the License for the specific language governing
 * permissions and limitations under the License.
 */

#include <emmintrin.h>
#include <immintrin.h>

#ifdef HAVE_MSVC_CPUIDEX
#include <intrin.h>
#endif

#include <aws/common/common.h>

#define CPUID_UNKNOWN 2
#define CPUID_AVAILABLE 0
#define CPUID_UNAVAILABLE 1
static int cpuid_state = 2;

bool aws_common_private_has_avx2() {
    if (AWS_LIKELY(cpuid_state == 0))
        return true;
    if (AWS_LIKELY(cpuid_state == 1))
        return false;

    /* Provide a hook for testing fallbacks and benchmarking */
    const char *env_avx2_enabled = getenv("AWS_COMMON_AVX2");
    if (env_avx2_enabled) {
        int is_enabled = atoi(env_avx2_enabled);
        cpuid_state = !is_enabled;
        return is_enabled;
    }

#ifdef HAVE_BUILTIN_CPU_SUPPORTS
    bool available = __builtin_cpu_supports("avx2");
#elif defined(HAVE_MAY_I_USE)
    bool available = _may_i_use_cpu_feature(_FEATURE_AVX2);
#elif defined(HAVE_MSVC_CPUIDEX)
#error TODO
#else
#error No CPUID probe mechanism available
#endif
    cpuid_state = available ? CPUID_AVAILABLE : CPUID_UNAVAILABLE;

    return available;
}
