/*
 * Copyright 2019 Amazon.com, Inc. or its affiliates. All Rights Reserved.
 *
 * Licensed under the Apache License, Version 2.0 (the "License"). You may not use
 * this file except in compliance with the License. A copy of the License is
 * located at
 *
 *     http://aws.amazon.com/apache2.0/
 *
 * or in the "license" file accompanying this file. This file is distributed on an
 * "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or
 * implied. See the License for the specific language governing permissions and
 * limitations under the License.
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
