#include <aws/common/math.h>
#include <proof_helpers.h>

/**
 * Multiplies a * b and returns the result in *r. If the result
 * overflows, returns AWS_OP_ERR; otherwise returns AWS_OP_SUCCESS.
 */
AWS_STATIC_IMPL int __aws_mul_u64_checked(uint64_t a, uint64_t b, uint64_t *r) {
    uint64_t x = a * b;
    *r = x;
    if (a != 0 && (a > UINT32_MAX || b > UINT32_MAX) && x / a != b) {
        return aws_raise_error(AWS_ERROR_OVERFLOW_DETECTED);
    }
    return AWS_OP_SUCCESS;
}

/**
 * Multiplies a * b and returns the result in *r. If the result
 * overflows, returns AWS_OP_ERR; otherwise returns AWS_OP_SUCCESS.
 */
AWS_STATIC_IMPL int __aws_mul_u32_checked(uint32_t a, uint32_t b, uint32_t *r) {
    uint32_t x = a * b;
    *r = x;
    if (a != 0 && (a > UINT16_MAX || b > UINT16_MAX) && x / a != b) {
        return aws_raise_error(AWS_ERROR_OVERFLOW_DETECTED);
    }
    return AWS_OP_SUCCESS;
}

/**
 * Runtime: 0m3.872s
 */
void aws_mul_size_checked_harness() {
    size_t r = nondet_size_t();
    size_t __r = nondet_size_t();
    __CPROVER_assume(r == __r);

    if (nondet_int()) {
        /*
         * In this particular case, full range of nondet inputs leads
         * to excessively long runtimes, so use UINT64_MAX instead.
         */
        uint64_t a = UINT64_MAX;
        uint64_t b = nondet_uint64_t();
        if (aws_mul_u64_checked(a, b, &r) == AWS_OP_SUCCESS && __aws_mul_u64_checked(a, b, &__r) == AWS_OP_SUCCESS)
            assert(r == __r);
    } else {
        /*
         * In this particular case, full range of nondet inputs leads
         * to excessively long runtimes, so use UINT32_MAX instead.
         */
        uint32_t a = UINT32_MAX;
        uint32_t b = nondet_uint32_t();
        if (aws_mul_u32_checked(a, b, &r) == AWS_OP_SUCCESS && __aws_mul_u32_checked(a, b, &__r) == AWS_OP_SUCCESS)
            assert(r == __r);
    }
}
