/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/common/math.h>

void aws_is_power_of_two_harness() {
    size_t test_val;
    bool rval = aws_is_power_of_two(test_val);
#if ULONG_MAX == SIZE_MAX
    int popcount = __builtin_popcountl(test_val);
#elif ULLONG_MAX == SIZE_MAX
    int popcount = __builtin_popcountll(test_val);
#else
#    error
#endif
    assert(rval == (popcount == 1));
}
