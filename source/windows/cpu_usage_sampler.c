/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/common/cpu_usage_sampler.h>
#include <aws/common/private/cpu_usage_sampler_private.h>

/*********************************************************************************************************************
 * Public operations
 ********************************************************************************************************************/

struct aws_cpu_sampler *aws_cpu_sampler_new(struct aws_allocator *allocator) {
    // OS currently not supported
    (void)(allocator);
    aws_raise_error(AWS_ERROR_PLATFORM_NOT_SUPPORTED);
    return NULL;
}
