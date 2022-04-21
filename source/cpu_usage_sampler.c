/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/common/cpu_usage_sampler.h>
#include <aws/common/private/cpu_usage_sampler_private.h>

/*********************************************************************************************************************
 * Public operations
 ********************************************************************************************************************/

void aws_system_cpu_sampler_destroy(struct aws_system_cpu_sampler *sampler) {
    if (sampler == NULL) {
        return;
    }
    sampler->vtable->destroy(sampler);
}

int aws_system_cpu_sampler_get_sample(struct aws_system_cpu_sampler *sampler, double *output) {
    return sampler->vtable->get_sample(sampler, output);
}
