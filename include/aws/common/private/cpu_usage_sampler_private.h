#ifndef AWS_COMMON_PRIVATE_CPU_USAGE_SAMPLER_PRIVATE_H
#define AWS_COMMON_PRIVATE_CPU_USAGE_SAMPLER_PRIVATE_H

/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/common/common.h>
#include <aws/common/math.h>

/**
 * The VTable for the CPU sampler in cpu_usage_sampler.h
 */
struct aws_cpu_sampler_vtable {
    int (*aws_get_cpu_sample_fn)(struct aws_cpu_sampler *sampler, double *output);
    void (*aws_cpu_sampler_destroy)(struct aws_cpu_sampler *sampler);
};

/**
 * The CPU sampler in cpu_usage_sampler.h
 */
struct aws_cpu_sampler {
    const struct aws_cpu_sampler_vtable *vtable;
    struct aws_allocator *allocator;
    void *impl;
};

#endif /* AWS_COMMON_PRIVATE_CPU_USAGE_SAMPLER_PRIVATE_H */
