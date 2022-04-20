/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/common/cpu_usage_sampler.h>
#include <aws/common/private/cpu_usage_sampler_private.h>

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
