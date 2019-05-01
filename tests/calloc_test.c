/*
 * Copyright 2019 Amazon.com, Inc. or its affiliates. All Rights Reserved.
 *
 * Licensed under the Apache License, Version 2.0 (the "License").
 * You may not use this file except in compliance with the License.
 * A copy of the License is located at
 *
 *  http://aws.amazon.com/apache2.0
 *
 * or in the "license" file accompanying this file. This file is distributed
 * on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 * express or implied. See the License for the specific language governing
 * permissions and limitations under the License.
 */

#include <aws/common/common.h>
#include <aws/common/math.h>
#include <aws/testing/aws_test_harness.h>

#ifdef __MACH__
#    include <CoreFoundation/CoreFoundation.h>
#endif

AWS_TEST_CASE(test_calloc_fallback, s_test_calloc_fallback_fn)
static int s_test_calloc_fallback_fn(struct aws_allocator *allocator, void *ctx) {
    struct aws_allocator my_alloc = *aws_default_allocator();
    my_alloc.mem_calloc = NULL;

    /* Check that calloc gives 0ed memory */
    char *p = aws_mem_calloc(&my_alloc, 2, 4);
    ASSERT_NOT_NULL(p);
    for (size_t i = 0; i < 2 * 4; ++i) {
        ASSERT_TRUE(p[i] == 0);
    }
    aws_mem_release(&my_alloc, p);
    /* Check that calloc handles overflow securely, by returning null
     * Choose values such that [small_val == (small_val)*(large_val)(mod 2**SIZE_BITS)]
     */
    for (size_t small_bits = 1; small_bits < 9; ++small_bits) {
        size_t large_bits = SIZE_BITS - small_bits;
        size_t small_val = (size_t)1 << small_bits;
        size_t large_val = ((size_t)1 << large_bits) + 1;
        ASSERT_TRUE(small_val * large_val == small_val);
        ASSERT_NULL(aws_mem_calloc(&my_alloc, small_val, large_val));
    }
    return 0;
}

AWS_TEST_CASE(test_calloc_from_default_allocator, s_test_calloc_from_default_allocator_fn)
static int s_test_calloc_from_default_allocator_fn(struct aws_allocator *allocator, void *ctx) {
    struct aws_allocator *alloc = aws_default_allocator();
    /* Check that calloc gives 0ed memory */
    char *p = aws_mem_calloc(alloc, 2, 4);
    ASSERT_NOT_NULL(p);
    for (size_t i = 0; i < 2 * 4; ++i) {
        ASSERT_TRUE(p[i] == 0);
    }
    aws_mem_release(alloc, p);
    /* Check that calloc handles overflow securely, by returning null
     * Choose values such that [small_val == (small_val)*(large_val)(mod 2**SIZE_BITS)]
     */
    for (size_t small_bits = 1; small_bits < 9; ++small_bits) {
        size_t large_bits = SIZE_BITS - small_bits;
        size_t small_val = (size_t)1 << small_bits;
        size_t large_val = ((size_t)1 << large_bits) + 1;
        ASSERT_TRUE(small_val * large_val == small_val);
        ASSERT_NULL(aws_mem_calloc(alloc, small_val, large_val));
    }
    return 0;
}
