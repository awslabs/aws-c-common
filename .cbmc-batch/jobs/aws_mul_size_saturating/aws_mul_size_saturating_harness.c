#include <aws/common/math.h>
#include <proof_helpers/make_common_data_structures.h>

/**
 * Coverage: 1.00 (24 lines out of 24 statically-reachable lines in 3 functions reached)
 * Runtime: 0m2.962s
 *
 * Assumptions:
 *     - given 2 non-deterministics unsigned integers
 *
 * Assertions:
 *     - if a * b overflows, aws_mul_u32_saturating and aws_mul_u64_saturating
 *       functions must always return the corresponding saturated value
 */
void aws_mul_size_saturating_harness() {
    if (nondet_bool()) {
        /*
         * In this particular case, full range of nondet inputs leads
         * to excessively long runtimes, so use 0 or UINT64_MAX instead.
         */
        uint64_t a = (nondet_int()) ? 0 : UINT64_MAX;
        uint64_t b = nondet_uint64_t();
        uint64_t r = aws_mul_u64_saturating(a, b);
        if (a > 0 && b > 0 && a > (UINT64_MAX / b)) {
            assert(r == UINT64_MAX);
        } else {
            assert(r == a * b);
        }
    } else {
        /*
         * In this particular case, full range of nondet inputs leads
         * to excessively long runtimes, so use 0 or UINT32_MAX instead.
         */
        uint32_t a = (nondet_bool()) ? 0 : UINT32_MAX;
        uint32_t b = nondet_uint32_t();
        uint32_t r = aws_mul_u32_saturating(a, b);
        if (a > 0 && b > 0 && a > (UINT32_MAX / b)) {
            assert(r == UINT32_MAX);
        } else {
            assert(r == a * b);
        }
    }
}
