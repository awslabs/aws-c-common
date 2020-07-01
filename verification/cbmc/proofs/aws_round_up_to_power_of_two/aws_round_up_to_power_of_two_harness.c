/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/common/math.h>

void aws_round_up_to_power_of_two_harness() {
    size_t test_val;
    size_t result;
    int rval = aws_round_up_to_power_of_two(test_val, &result);

#if ULONG_MAX == SIZE_MAX
    int popcount = __builtin_popcountl(result);
#elif ULLONG_MAX == SIZE_MAX
    int popcount = __builtin_popcountll(result);
#else
#    error
#endif
    if (rval == AWS_OP_SUCCESS) {
        assert(popcount == 1);
        assert(test_val <= result);
        assert(test_val >= result >> 1);
    } else {
        // Only fail if rounding up would cause us to overflow.
        assert(test_val > ((SIZE_MAX >> 1) + 1));
    }
}
