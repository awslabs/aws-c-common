/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/common/system_resource_util.h>

#include <aws/testing/aws_test_harness.h>

static int s_test_memory_usage_maxrss(struct aws_allocator *allocator, void *ctx) {
    (void)allocator;
    (void)ctx;

    struct aws_memory_usage_stats mu;
    ASSERT_SUCCESS(aws_init_memory_usage_for_current_process(&mu));

    ASSERT_TRUE(mu.maxrss > 0);

    return 0;
}

AWS_TEST_CASE(test_memory_usage_maxrss, s_test_memory_usage_maxrss)
