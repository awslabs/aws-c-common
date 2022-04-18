/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/common/cpu_usage_sampler.h>

/*********************************************************************************************************************
 * Base implementation
 ********************************************************************************************************************/

struct aws_cpu_sampler_vtable {
    int (*aws_get_cpu_sample_fn)(struct aws_cpu_sampler *sampler, double *output);
    void (*aws_cpu_sampler_destroy)(struct aws_cpu_sampler *sampler);
};

struct aws_cpu_sampler {
    const struct aws_cpu_sampler_vtable *vtable;
    struct aws_allocator *allocator;
    void *impl;
};

static void aws_cpu_sampler_destroy_default(struct aws_cpu_sampler *sampler) {
    if (sampler == NULL) {
        return;
    }
    aws_mem_release(sampler->allocator, sampler);
}

static struct aws_cpu_sampler_vtable aws_cpu_sampler_vtable_default = {
    .aws_get_cpu_sample_fn = NULL,
    .aws_cpu_sampler_destroy = aws_cpu_sampler_destroy_default,
};

/*********************************************************************************************************************
 * Public operations
 ********************************************************************************************************************/

struct aws_cpu_sampler *aws_cpu_sampler_new(struct aws_allocator *allocator) {
    if (allocator == NULL) {
        aws_raise_error(AWS_ERROR_INVALID_ARGUMENT);
        return NULL;
    }

    // OS not supported
    struct aws_cpu_sampler *output_unsupported = aws_mem_calloc(allocator, 1, sizeof(struct aws_cpu_sampler));
    output_unsupported->allocator = allocator;
    output_unsupported->impl = NULL;
    output_unsupported->vtable = &aws_cpu_sampler_vtable_default;
    return output_unsupported;
}
