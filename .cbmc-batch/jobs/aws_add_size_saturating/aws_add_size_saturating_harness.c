#include <aws/common/math.h>
#include <proof_helpers/make_common_data_structures.h>

/**
 * Coverage: 1.00 (24 lines out of 24 statically-reachable lines in 3 functions reached)
 * Runtime: 0m2.698s
 *
 * Assumptions:
 *     - given 2 non-deterministics unsigned integers
 *
 * Assertions:
 *     - if a + b overflows, aws_add_u32_saturating and aws_add_u64_saturating
 *       functions must always return the corresponding saturated value
 */
void aws_add_size_saturating_harness() {
    if (nondet_bool()) {
        uint64_t a = nondet_uint64_t();
        uint64_t b = nondet_uint64_t();
        uint64_t r = aws_add_u64_saturating(a, b);
        if ((b > 0) && (a > (UINT64_MAX - b))) {
            assert(r == UINT64_MAX);
        } else {
            assert(r == a + b);
        }
    } else {
        uint32_t a = nondet_uint32_t();
        uint32_t b = nondet_uint32_t();
        uint32_t r = aws_add_u32_saturating(a, b);
        if ((b > 0) && (a > (UINT32_MAX - b))) {
            assert(r == UINT32_MAX);
        } else {
            assert(r == a + b);
        }
    }
}
