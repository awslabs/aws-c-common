/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/common/byte_buf.h>
#include <aws/common/device_random.h>
#include <aws/common/system_resource_util.h>

#include <aws/testing/aws_test_harness.h>

static int s_test_memory_usage_maxrss(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;

    /*
     * Note: mem usage apis currently rely on getrusage on posix systems.
     * On freebsd maxrss seems to return current process rss based on testing,
     * while on every other posix platform maxrss is high water mark for rss
     * over the program lifetime.
     * Workaround it by allocating a buffer first. Long term using procfs should
     * avoid the issue.
     */
    struct aws_byte_buf temp;
    aws_byte_buf_init(&temp, allocator, 8 * 1024 * 1024);
    ASSERT_SUCCESS(aws_device_random_buffer(&temp));

    struct aws_memory_usage_stats mu;
    ASSERT_SUCCESS(aws_init_memory_usage_for_current_process(&mu));

    ASSERT_TRUE(mu.maxrss > 0);

    aws_byte_buf_clean_up_secure(&temp);

    return 0;
}

AWS_TEST_CASE(test_memory_usage_maxrss, s_test_memory_usage_maxrss)
