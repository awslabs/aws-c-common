#ifndef AWS_COMMON_PRIVATE_SYSTEM_CPU_USAGE_SAMPLER_PRIVATE_H
#define AWS_COMMON_PRIVATE_SYSTEM_CPU_USAGE_SAMPLER_PRIVATE_H

/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/common/common.h>
#include <aws/common/system_info.h>

/**
 * The VTable for the CPU sampler in cpu_usage_sampler.h
 */
struct aws_system_cpu_sampler_vtable {
    int (*get_sample)(struct aws_system_cpu_sampler *sampler, double *output);
    void (*destroy)(struct aws_system_cpu_sampler *sampler);
};

/**
 * The CPU sampler in cpu_usage_sampler.h
 */
struct aws_system_cpu_sampler {
    const struct aws_system_cpu_sampler_vtable *vtable;
    struct aws_allocator *allocator;
    void *impl;
};

#endif /* AWS_COMMON_PRIVATE_SYSTEM_CPU_USAGE_SAMPLER_PRIVATE_H */
