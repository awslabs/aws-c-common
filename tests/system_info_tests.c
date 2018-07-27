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

#include <aws/common/system_info.h>

#include <aws/testing/aws_test_harness.h>

static int s_test_cpu_count_at_least_works_superficially_fn(struct aws_allocator *allocator, void *ctx) {
    (void)allocator;
    (void)ctx;

    size_t processor_count = aws_system_info_processor_count();
    /* I think this is a fairly reasonable assumption given the circumstances
     * (you know this test is part of a program
     * that must be running on at least one core).... */
    ASSERT_TRUE(processor_count > 0);

    return 0;
}

AWS_TEST_CASE(test_cpu_count_at_least_works_superficially, s_test_cpu_count_at_least_works_superficially_fn)
