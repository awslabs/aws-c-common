/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/common/private/system_cpu_usage_sampler_private.h>
#include <aws/common/system_info.h>

/*********************************************************************************************************************
 * Public operations
 ********************************************************************************************************************/

struct aws_system_cpu_sampler *aws_system_cpu_sampler_new(struct aws_allocator *allocator) {
    // OS currently not supported
    (void)(allocator);
    aws_raise_error(AWS_ERROR_PLATFORM_NOT_SUPPORTED);
    return NULL;
}
