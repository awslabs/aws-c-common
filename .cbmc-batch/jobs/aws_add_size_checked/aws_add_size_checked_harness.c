#include <aws/common/math.h>
#include <proof_helpers/make_common_data_structures.h>

/**
 * Coverage: 1.00 (29 lines out of 29 statically-reachable lines in 5 functions reached)
 * Runtime: 0m2.025s
 *
 * Assumptions:
 *     - For any given inputs, r will never overflow, if aws_add_u32_checked or
 *       aws_add_u64_checked functions return AWS_OP_SUCCESS.
 */
void aws_add_size_checked_harness() {
    if (nondet_int()) {
        uint64_t a = nondet_uint64_t();
        uint64_t b = nondet_uint64_t();
        uint64_t r = nondet_uint64_t();
        if (!aws_add_u64_checked(a, b, &r))
            assert(r == a + b);
    } else {
        uint32_t a = nondet_uint32_t();
        uint32_t b = nondet_uint32_t();
        uint32_t r = nondet_uint32_t();
        if (!aws_add_u32_checked(a, b, &r))
            assert(r == a + b);
    }
}
