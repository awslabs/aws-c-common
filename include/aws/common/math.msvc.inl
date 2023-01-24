#ifndef AWS_COMMON_MATH_MSVC_INL
#define AWS_COMMON_MATH_MSVC_INL

/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

/*
 * This header is already included, but include it again to make editor
 * highlighting happier.
 */
#include <aws/common/common.h>
#include <aws/common/cpuid.h>
#include <aws/common/math.h>

#include <immintrin.h>
#include <intrin.h>

AWS_EXTERN_C_BEGIN
/**
 * Multiplies a * b. If the result overflows, returns 2^64 - 1.
 */
AWS_STATIC_IMPL uint64_t aws_mul_u64_saturating(uint64_t a, uint64_t b) {
    uint64_t out;
    uint64_t ret_val = _umul128(a, b, &out);
    return (out == 0) ? ret_val : UINT64_MAX;
}

/**
 * If a * b overflows, returns AWS_OP_ERR; otherwise multiplies
 * a * b, returns the result in *r, and returns AWS_OP_SUCCESS.
 */
AWS_STATIC_IMPL int aws_mul_u64_checked(uint64_t a, uint64_t b, uint64_t *r) {
    uint64_t out;
    *r = _umul128(a, b, &out);

    if (out != 0) {
        return aws_raise_error(AWS_ERROR_OVERFLOW_DETECTED);
    }
    return AWS_OP_SUCCESS;
}

/**
 * Multiplies a * b. If the result overflows, returns 2^32 - 1.
 */
AWS_STATIC_IMPL uint32_t aws_mul_u32_saturating(uint32_t a, uint32_t b) {
    if (aws_cpu_has_feature(AWS_CPU_FEATURE_BMI2)) {
        uint32_t high_32;
        uint32_t ret_val = _mulx_u32(a, b, &high_32);
        return (high_32 == 0) ? ret_val : UINT32_MAX;
    } else {
        /* If BMI2 unavailable, use __emulu instead */
        uint64_t result = __emulu(a, b);
        return (result > UINT32_MAX) ? UINT32_MAX : (uint32_t)result;
    }
}

/**
 * If a * b overflows, returns AWS_OP_ERR; otherwise multiplies
 * a * b, returns the result in *r, and returns AWS_OP_SUCCESS.
 */
AWS_STATIC_IMPL int aws_mul_u32_checked(uint32_t a, uint32_t b, uint32_t *r) {
    if (aws_cpu_has_feature(AWS_CPU_FEATURE_BMI2)) {
        uint32_t high_32;
        *r = _mulx_u32(a, b, &high_32);

        if (high_32 != 0) {
            return aws_raise_error(AWS_ERROR_OVERFLOW_DETECTED);
        }
    } else {
        /* If BMI2 unavailable, use __emulu instead */
        uint64_t result = __emulu(a, b);
        if (result > UINT32_MAX) {
            return aws_raise_error(AWS_ERROR_OVERFLOW_DETECTED);
        }
        *r = (uint32_t)result;
    }
    return AWS_OP_SUCCESS;
}

/**
 * If a + b overflows, returns AWS_OP_ERR; otherwise adds
 * a + b, returns the result in *r, and returns AWS_OP_SUCCESS.
 */
AWS_STATIC_IMPL int aws_add_u64_checked(uint64_t a, uint64_t b, uint64_t *r) {
    uint8_t c_in = 0u;
    uint8_t c_out = _addcarry_u64(c_in, a, b, r);
    printf("a:%llu   b:%llu  res:%llu   c_in:%c  c_out: %c\n", a, b, *r, c_in, c_out);
    if (c_out) {
        return aws_raise_error(AWS_ERROR_OVERFLOW_DETECTED);
    }
    return AWS_OP_SUCCESS;
}

/**
 * Adds a + b. If the result overflows, returns 2^64 - 1.
 */
AWS_STATIC_IMPL uint64_t aws_add_u64_saturating(uint64_t a, uint64_t b) {
    uint64_t res = 0;
    uint8_t c_in = 0u;
    uint8_t c_out = _addcarry_u64(c_in, a, b, &res);
    printf("a:%llu   b:%llu  res:%llu   c_in:%c  c_out: %c\n", a, b, res, c_in, c_out);

    if (c_out) {
        res = UINT64_MAX;
    }

    return res;
}

/**
 * If a + b overflows, returns AWS_OP_ERR; otherwise adds
 * a + b, returns the result in *r, and returns AWS_OP_SUCCESS.
 */
AWS_STATIC_IMPL int aws_add_u32_checked(uint32_t a, uint32_t b, uint32_t *r) {
    uint8_t c_in = 0u;
    if (_addcarry_u32(c_in, a, b, r)) {
        return aws_raise_error(AWS_ERROR_OVERFLOW_DETECTED);
    }
    return AWS_OP_SUCCESS;
}

/**
 * Adds a + b. If the result overflows, returns 2^32 - 1.
 */
AWS_STATIC_IMPL uint32_t aws_add_u32_saturating(uint32_t a, uint32_t b) {
    uint32_t res = 0;
    uint8_t c_in = 0u;

    if (_addcarry_u32(c_in, a, b, &res)) {
        res = UINT32_MAX;
    }

    return res;
}

/**
 * Search from the MSB to LSB, looking for a 1
 */
AWS_STATIC_IMPL size_t aws_clz_u32(uint32_t n) {
    unsigned long idx = 0;
    if (_BitScanReverse(&idx, n)) {
        return 31 - idx;
    }
    return 32;
}

AWS_STATIC_IMPL size_t aws_clz_i32(int32_t n) {
    unsigned long idx = 0;
    if (_BitScanReverse(&idx, n)) {
        return 31 - idx;
    }
    return 32;
}

AWS_STATIC_IMPL size_t aws_clz_u64(uint64_t n) {
    unsigned long idx = 0;
    if (_BitScanReverse64(&idx, n)) {
        return 63 - idx;
    }
    return 64;
}

AWS_STATIC_IMPL size_t aws_clz_i64(int64_t n) {
    unsigned long idx = 0;
    if (_BitScanReverse64(&idx, n)) {
        return 63 - idx;
    }
    return 64;
}

AWS_STATIC_IMPL size_t aws_clz_size(size_t n) {
#if SIZE_BITS == 64
    return aws_clz_u64(n);
#else
    return aws_clz_u32(n);
#endif
}

/**
 * Search from the LSB to MSB, looking for a 1
 */
AWS_STATIC_IMPL size_t aws_ctz_u32(uint32_t n) {
    unsigned long idx = 0;
    if (_BitScanForward(&idx, n)) {
        return idx;
    }
    return 32;
}

AWS_STATIC_IMPL size_t aws_ctz_i32(int32_t n) {
    unsigned long idx = 0;
    if (_BitScanForward(&idx, n)) {
        return idx;
    }
    return 32;
}

AWS_STATIC_IMPL size_t aws_ctz_u64(uint64_t n) {
    unsigned long idx = 0;
    if (_BitScanForward64(&idx, n)) {
        return idx;
    }
    return 64;
}

AWS_STATIC_IMPL size_t aws_ctz_i64(int64_t n) {
    unsigned long idx = 0;
    if (_BitScanForward64(&idx, n)) {
        return idx;
    }
    return 64;
}

AWS_STATIC_IMPL size_t aws_ctz_size(size_t n) {
#if SIZE_BITS == 64
    return aws_ctz_u64(n);
#else
    return aws_ctz_u32(n);
#endif
}

AWS_EXTERN_C_END
#endif /* WS_COMMON_MATH_MSVC_INL */
