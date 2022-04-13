#ifndef AWS_COMMON_CPU_USAGE_SAMPLER_H
#define AWS_COMMON_CPU_USAGE_SAMPLER_H

/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/common/common.h>
#include <aws/common/math.h>

AWS_EXTERN_C_BEGIN

struct cpu_usage_sampler {
    struct aws_allocator *allocator;
};

AWS_COMMON_API
int aws_cpu_sampler_new(struct aws_allocator *allocator, struct cpu_usage_sampler *sampler);
void aws_cpu_sampler_cleanup(struct cpu_usage_sampler *sampler);
int aws_cpu_sampler_get_sample(struct cpu_usage_sampler *sampler, double *output);

AWS_EXTERN_C_END

// Platform specific bindings
// Linux
#if defined(__linux__) || defined(__unix__)
struct cpu_usage_sampler_linux {
    struct aws_allocator *allocator;
    uint64_t *cpu_last_total_user;
    uint64_t *cpu_last_total_user_low;
    uint64_t *cpu_last_total_system;
    uint64_t *cpu_last_total_idle;
};
const int sample_usage_linux(struct cpu_usage_sampler_linux *sampler, double *output);
#endif // Linux

#endif /* AWS_COMMON_CPU_USAGE_SAMPLER_H */
