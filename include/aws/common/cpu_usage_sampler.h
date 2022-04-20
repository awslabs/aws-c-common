#ifndef AWS_COMMON_CPU_USAGE_SAMPLER_H
#define AWS_COMMON_CPU_USAGE_SAMPLER_H

/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/common/common.h>
#include <aws/common/math.h>

/**
 * A struct that contains the CPU sampler for this platform.
 * Currently only Linux is supported.
 *
 * Note: Must be freed from memory using aws_cpu_sampler_destroy when finished.
 */
struct aws_cpu_sampler;

AWS_EXTERN_C_BEGIN

/**
 * Creates a new CPU sampler using the provided allocator, or will return NULL if there is an error.
 *
 * Note: On unsupported platforms, the CPU sampler returned will return AWS_OP_ERR when calling
 * aws_cpu_sampler_get_sample. You will still need to call aws_cpu_sampler_clean_up when finished
 * to free the memory even for unsupported platforms.
 */
AWS_COMMON_API
struct aws_cpu_sampler *aws_cpu_sampler_new(struct aws_allocator *allocator);

/**
 * Frees the memory used by the CPU sampler.
 */
AWS_COMMON_API
void aws_cpu_sampler_destroy(struct aws_cpu_sampler *sampler);

/**
 * Gets the CPU usage and populates the given double, output, with the value. The value
 * returned is a percentage from 0.0 to 100.0.
 *
 * Will return AWS_OP_SUCCESS if polling the CPU was successful. AWS_OP_ERR will be returned
 * if the result should not be used or if there was an error polling the CPU.
 *
 * Will always return AWS_OP_ERR for unsupported platforms.
 */
AWS_COMMON_API
int aws_cpu_sampler_get_sample(struct aws_cpu_sampler *sampler, double *output);

AWS_EXTERN_C_END

#endif /* AWS_COMMON_CPU_USAGE_SAMPLER_H */
