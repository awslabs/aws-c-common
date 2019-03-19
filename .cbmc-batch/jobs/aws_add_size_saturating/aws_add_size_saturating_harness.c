#include <aws/common/math.h>
#include <proof_helpers/make_common_data_structures.h>

/**
 * Adds a + b.  If the result overflows returns 2^64 - 1.
 */
AWS_STATIC_IMPL uint64_t __aws_add_u64_saturating(uint64_t a, uint64_t b) {
    uint64_t x = a + b;
    if (x < a) {
        return UINT64_MAX;
    }
    return x;
}

/**
 * Adds a + b. If the result overflows returns 2^32 - 1.
 */
AWS_STATIC_IMPL uint32_t __aws_add_u32_saturating(uint32_t a, uint32_t b) {
    uint32_t x = a + b;
    if (x < a) {
        return UINT32_MAX;
    }
    return x;
}

/**
 * Runtime: 0m2.608s
 */
void aws_add_size_saturating_harness() {
    if (nondet_int()) {
        uint64_t a = nondet_uint64_t();
        uint64_t b = nondet_uint64_t();
        assert(aws_add_u64_saturating(a, b) == __aws_add_u64_saturating(a, b));
    } else {
        uint32_t a = nondet_uint32_t();
        uint32_t b = nondet_uint32_t();
        assert(aws_add_u32_saturating(a, b) == __aws_add_u32_saturating(a, b));
    }
}
