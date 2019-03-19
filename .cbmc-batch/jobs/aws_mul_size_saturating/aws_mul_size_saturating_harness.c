#include <aws/common/math.h>
#include <proof_helpers/make_common_data_structures.h>

/**
 * Multiplies a * b. If the result overflows, returns 2^64 - 1.
 */
AWS_STATIC_IMPL uint64_t __aws_mul_u64_saturating(uint64_t a, uint64_t b) {
    uint64_t x = a * b;
    if (a != 0 && (a > UINT32_MAX || b > UINT32_MAX) && x / a != b) {
        return UINT64_MAX;
    }
    return x;
}

/**
 * Multiplies a * b. If the result overflows, returns 2^32 - 1.
 */
AWS_STATIC_IMPL uint32_t __aws_mul_u32_saturating(uint32_t a, uint32_t b) {
    uint32_t x = a * b;
    if (a != 0 && (a > UINT16_MAX || b > UINT16_MAX) && x / a != b) {
        return UINT32_MAX;
    }
    return x;
}

/**
 * Runtime: 0m3.393s
 */
void aws_mul_size_saturating_harness() {
    if (nondet_int()) {
        /*
         * In this particular case, full range of nondet inputs leads
         * to excessively long runtimes, so use UINT64_MAX instead.
         */
        uint64_t a = UINT64_MAX;
        uint64_t b = nondet_uint64_t();
        assert(aws_mul_u64_saturating(a, b) == __aws_mul_u64_saturating(a, b));
    } else {
        /*
         * In this particular case, full range of nondet inputs leads
         * to excessively long runtimes, so use UINT32_MAX instead.
         */
        uint32_t a = UINT32_MAX;
        uint32_t b = nondet_uint32_t();
        assert(aws_mul_u32_saturating(a, b) == __aws_mul_u32_saturating(a, b));
    }
}
