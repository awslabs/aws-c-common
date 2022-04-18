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

/*********************************************************************************************************************
 * Public operations
 ********************************************************************************************************************/

void aws_cpu_sampler_destroy(struct aws_cpu_sampler *sampler) {
    if (sampler == NULL) {
        return;
    }
    if (sampler->vtable->aws_cpu_sampler_destroy == NULL) {
        return;
    }
    sampler->vtable->aws_cpu_sampler_destroy(sampler);
}

int aws_cpu_sampler_get_sample(struct aws_cpu_sampler *sampler, double *output) {
    if (sampler == NULL) {
        aws_raise_error(AWS_ERROR_INVALID_ARGUMENT);
        return AWS_OP_ERR;
    }
    if (sampler->vtable->aws_get_cpu_sample_fn == NULL) {
        aws_raise_error(AWS_ERROR_PLATFORM_NOT_SUPPORTED);
        return AWS_OP_ERR;
    }
    return sampler->vtable->aws_get_cpu_sample_fn(sampler, output);
}
