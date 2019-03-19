#include <aws/common/math.h>
#include <proof_helpers/make_common_data_structures.h>

/**
 * Adds a + b and returns the result in *r. If the result
 * overflows, returns AWS_OP_ERR; otherwise returns AWS_OP_SUCCESS.
 */
AWS_STATIC_IMPL int __aws_add_u64_checked(uint64_t a, uint64_t b, uint64_t *r) {
    uint64_t x = a + b;
    *r = x;
    if (x < a) {
        return aws_raise_error(AWS_ERROR_OVERFLOW_DETECTED);
    }
    return AWS_OP_SUCCESS;
}

/**
 * Adds a + b and returns the result in *r. If the result
 * overflows, returns AWS_OP_ERR; otherwise returns AWS_OP_SUCCESS.
 */
AWS_STATIC_IMPL int __aws_add_u32_checked(uint32_t a, uint32_t b, uint32_t *r) {
    uint32_t x = a + b;
    *r = x;
    if (x < a) {
        return aws_raise_error(AWS_ERROR_OVERFLOW_DETECTED);
    }
    return AWS_OP_SUCCESS;
}

/**
 * Runtime: 0m2.025s
 */
void aws_add_size_checked_harness() {
    size_t r = nondet_size_t();
    size_t __r = nondet_size_t();
    __CPROVER_assume(r == __r);

    if (nondet_int()) {
        uint64_t a = nondet_uint64_t();
        uint64_t b = nondet_uint64_t();
        if (aws_add_u64_checked(a, b, &r) == AWS_OP_SUCCESS && __aws_add_u64_checked(a, b, &__r) == AWS_OP_SUCCESS)
            assert(r == __r);
    } else {
        uint32_t a = nondet_uint32_t();
        uint32_t b = nondet_uint32_t();
        if (aws_add_u32_checked(a, b, &r) == AWS_OP_SUCCESS && __aws_add_u32_checked(a, b, &__r) == AWS_OP_SUCCESS)
            assert(r == __r);
    }
}
