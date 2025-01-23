/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

/*
 * MSVC wants us to use the non-portable _dupenv_s instead; since we need
 * to remain portable, tell MSVC to suppress this warning.
 */
#define _CRT_SECURE_NO_WARNINGS

#include <aws/common/cpuid.h>
#include <stdlib.h>

extern void aws_run_cpuid(uint32_t eax, uint32_t ecx, uint32_t *abcd);
extern uint64_t aws_run_xgetbv(uint32_t xcr);

static bool s_cpu_features[AWS_CPU_FEATURE_COUNT];
static bool s_cpu_features_cached;

static void s_cache_cpu_features(void) {
    /* First, find the max EAX value we can pass to CPUID without undefined behavior */
    uint32_t abcd[4];
    aws_run_cpuid(0x0, 0x0, abcd);
    const uint32_t max_cpuid_value = abcd[0]; /* EAX */

#define RUN_CPUID_OR_RETURN(EAX, ECX)                                                                                  \
    do {                                                                                                               \
        if (max_cpuid_value < (EAX))                                                                                   \
            return;                                                                                                    \
        else                                                                                                           \
            aws_run_cpuid((EAX), (ECX), abcd);                                                                         \
    } while (0)

    /**************************************************************************
     * CPUID(EAX=1H, ECX=0H): Processor Info and Feature Bits
     **************************************************************************/
    RUN_CPUID_OR_RETURN(0x1, 0x0);
    s_cpu_features[AWS_CPU_FEATURE_CLMUL] = abcd[2] & (1 << 1);    /* ECX[bit 1] */
    s_cpu_features[AWS_CPU_FEATURE_SSE_4_1] = abcd[2] & (1 << 19); /* ECX[bit 19] */
    s_cpu_features[AWS_CPU_FEATURE_SSE_4_2] = abcd[2] & (1 << 20); /* ECX[bit 20] */

    /* NOTE: Even if the AVX flag is set, it's not necessarily usable.
     * We need to check that OSXSAVE is enabled, and check further capabilities via XGETBV.
     * GCC had the same bug until 7.4: https://gcc.gnu.org/bugzilla/show_bug.cgi?id=85100 */
    bool avx_usable = false;
    bool avx512_usable = false;
    bool feature_osxsave = abcd[2] & (1 << 27); /* ECX bit 27 */
    if (feature_osxsave) {
        uint64_t xcr0 = aws_run_xgetbv(0 /* 0 is _XCR_XFEATURE_ENABLED_MASK*/);
        const uint64_t avx_mask = (1 << 1) /* SSE = XCR0[bit 1] */
                                  | (1 << 2) /* AVX = XCR0[bit 2] */;
        avx_usable = (xcr0 & avx_mask) == avx_mask;

        const uint64_t avx512_mask = (1 << 5)   /* OPMASK = XCR0[bit 5] */
                                     | (1 << 6) /* ZMM_Hi256 = XCR0[bit 6] */
                                     | (1 << 7) /* Hi16_ZMM = XCR0[bit 7] */
                                     | avx_mask;
        avx512_usable = (xcr0 & avx512_mask) == avx512_mask;
    }

    bool feature_avx = false;
    if (avx_usable) {
        feature_avx = abcd[2] & (1 << 28); /* ECX bit 28 */
    }

    /***************************************************************************
     * CPUID(EAX=7H, ECX=0H): Extended Features
     **************************************************************************/
    RUN_CPUID_OR_RETURN(0x7, 0x0);
    s_cpu_features[AWS_CPU_FEATURE_BMI2] = abcd[1] & (1 << 8);        /* EBX[bit 8] */
    s_cpu_features[AWS_CPU_FEATURE_VPCLMULQDQ] = abcd[2] & (1 << 10); /* ECX[bit 10] */

    /* NOTE: It SHOULD be impossible for a CPU to support AVX2 without supporting AVX.
     * But we've received crash reports where the AVX2 feature check passed
     * and then an AVX instruction caused an "invalid instruction" crash.
     *
     * We diagnosed these machines by asking users to run the sample program from:
     * https://docs.microsoft.com/en-us/cpp/intrinsics/cpuid-cpuidex?view=msvc-160
     * and observed the following results:
     *
     *      AVX not supported
     *      AVX2 supported
     *
     * We don't know for sure what was up with those machines, but this extra
     * check should stop them from running our AVX/AVX2 code paths. */
    if (feature_avx) {
        if (avx512_usable) {
            s_cpu_features[AWS_CPU_FEATURE_AVX512] = abcd[1] & (1 << 16); /*  AVX-512 Foundation = EBX[bit 16] */
        }
    }
}

bool aws_cpu_has_feature(enum aws_cpu_feature_name feature_name) {
    if (AWS_UNLIKELY(!s_cpu_features_cached)) {
        s_cache_cpu_features();
        s_cpu_features_cached = true;
    }

    AWS_ASSERT(feature_name >= 0 && feature_name < AWS_CPU_FEATURE_COUNT);
    return s_cpu_features[feature_name];
}

#define CPUID_AVAILABLE 0
#define CPUID_UNAVAILABLE 1
static int cpuid_state = 2;

bool aws_common_private_has_avx2(void) {
    if (AWS_LIKELY(cpuid_state == 0)) {
        return true;
    }
    if (AWS_LIKELY(cpuid_state == 1)) {
        return false;
    }

    /* Provide a hook for testing fallbacks and benchmarking */
    const char *env_avx2_enabled = getenv("AWS_COMMON_AVX2");
    if (env_avx2_enabled) {
        int is_enabled = atoi(env_avx2_enabled);
        cpuid_state = !is_enabled;
        return is_enabled;
    }

    bool available = aws_cpu_has_feature(AWS_CPU_FEATURE_AVX2);
    cpuid_state = available ? CPUID_AVAILABLE : CPUID_UNAVAILABLE;

    return available;
}
