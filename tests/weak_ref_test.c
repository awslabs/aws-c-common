/*
 * Copyright 2010-2018 Amazon.com, Inc. or its affiliates. All Rights Reserved.
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

#include <aws/common/weak_ref.h>

#include <aws/common/string.h>

#include <aws/testing/aws_test_harness.h>

AWS_STATIC_STRING_FROM_LITERAL(s_test_data, "test");

static int s_weak_ref_test_basic(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;

    struct aws_weak_ref *ref = aws_weak_ref_new(allocator, (void *)s_test_data);
    ASSERT_TRUE(ref != NULL);

    struct aws_string *data = aws_weak_ref_lock(ref);
    ASSERT_TRUE(data == s_test_data);

    aws_weak_ref_unlock(ref);

    aws_weak_ref_set(ref, NULL);

    data = aws_weak_ref_lock(ref);
    ASSERT_TRUE(data == NULL);

    aws_weak_ref_release(ref);

    return 0;
}

AWS_TEST_CASE(weak_ref_test_basic, s_weak_ref_test_basic)

static int s_weak_ref_test_counting(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;

    struct aws_weak_ref *ref = aws_weak_ref_new(allocator, (void *)s_test_data);
    ASSERT_TRUE(ref != NULL);

    aws_weak_ref_acquire(ref);
    aws_weak_ref_acquire(ref);
    aws_weak_ref_acquire(ref);

    aws_weak_ref_release(ref);
    aws_weak_ref_release(ref);
    aws_weak_ref_release(ref);
    aws_weak_ref_release(ref);

    /* success = not leaking and not crashing */

    return 0;
}

AWS_TEST_CASE(weak_ref_test_counting, s_weak_ref_test_counting)