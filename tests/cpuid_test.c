/*
 * Copyright 2020 Amazon.com, Inc. or its affiliates. All Rights Reserved.
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

#include <aws/common/cpuid.h>
#include <aws/testing/aws_test_harness.h>

static int s_cpuid_test_fn(struct aws_allocator *allocator, void *ctx) {
    (void)allocator;
    (void)ctx;
    /* TODO: make sure those check returns the expected value. */
    aws_cpu_has_feature(AWS_CPU_FEATURE_CLMUL);
    aws_cpu_has_feature(AWS_CPU_FEATURE_SSE_4_1);
    aws_cpu_has_feature(AWS_CPU_FEATURE_SSE_4_2);
    aws_cpu_has_feature(AWS_CPU_FEATURE_AVX2);
    aws_cpu_has_feature(AWS_CPU_FEATURE_AVX512);
    aws_cpu_has_feature(AWS_CPU_FEATURE_ARM_CRC);
    aws_cpu_has_feature(AWS_CPU_FEATURE_BMI2);
    return AWS_OP_SUCCESS;
}

AWS_TEST_CASE(cpuid_test, s_cpuid_test_fn);
