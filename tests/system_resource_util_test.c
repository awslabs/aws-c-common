/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/common/system_resource_util.h>

#include <aws/testing/aws_test_harness.h>

static int s_test_resource_usage_maxrss(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;

    struct aws_resource_usage ru;
    AWS_ZERO_STRUCT(ru);
    ASSERT_SUCCESS(aws_resource_usage_for_current_process(&ru));

    ASSERT_TRUE(ru.maxrss > 0);

    return 0;
}

AWS_TEST_CASE(test_resource_usage_maxrss, s_test_resource_usage_maxrss)