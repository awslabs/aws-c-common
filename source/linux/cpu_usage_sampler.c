/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/common/cpu_usage_sampler.h>
#include <aws/common/private/cpu_usage_sampler_private.h>

#include <inttypes.h>
#include <sys/sysinfo.h>
#include <sys/types.h>

/*********************************************************************************************************************
 * Linux Specific
 ********************************************************************************************************************/

struct aws_cpu_sampler_linux {
    struct aws_cpu_sampler base;

    uint64_t cpu_last_total_user;
    uint64_t cpu_last_total_user_low;
    uint64_t cpu_last_total_system;
    uint64_t cpu_last_total_idle;
};

static void s_get_cpu_usage_linux(
    uint64_t *total_user,
    uint64_t *total_user_low,
    uint64_t *total_system,
    uint64_t *total_idle) {

    FILE *file;
    int matched_results;
    file = fopen("/proc/stat", "r");
    matched_results = fscanf(
        file,
        "cpu %" SCNu64 " %" SCNu64 " %" SCNu64 " %" SCNu64 "",
        (uint64_t *)total_user,
        (uint64_t *)total_user_low,
        (uint64_t *)total_system,
        (uint64_t *)total_idle);
    fclose(file);
    if (matched_results == EOF || matched_results != 4) {
        aws_raise_error(AWS_ERROR_INVALID_STATE);
    }
}

static void aws_get_cpu_sample_fn_linux_get_uint64_delta(uint64_t first, uint64_t second, uint64_t *output) {
    if (first > second) {
        aws_sub_u64_checked(first, second, output);
    } else {
        aws_add_u64_checked((UINT64_MAX - second), first, output);
    }
}

static int aws_get_cpu_sample_fn_linux(struct aws_cpu_sampler *sampler, double *output) {
    struct aws_cpu_sampler_linux *sampler_linux = sampler->impl;

    int return_result = AWS_OP_ERR;
    uint64_t total_user, total_user_low, total_system, total_idle, total;
    s_get_cpu_usage_linux(&total_user, &total_user_low, &total_system, &total_idle);
    // total_combined needs to be double to allow for fractions
    double percent, total_combined;

    uint64_t total_user_delta = 0, total_user_low_delta = 0, total_system_delta = 0, total_idle_delta = 0;
    aws_get_cpu_sample_fn_linux_get_uint64_delta(total_user, sampler_linux->cpu_last_total_user, &total_user_delta);
    aws_get_cpu_sample_fn_linux_get_uint64_delta(
        total_user_low, sampler_linux->cpu_last_total_user_low, &total_user_low_delta);
    aws_get_cpu_sample_fn_linux_get_uint64_delta(
        total_system, sampler_linux->cpu_last_total_system, &total_system_delta);
    aws_get_cpu_sample_fn_linux_get_uint64_delta(total_idle, sampler_linux->cpu_last_total_idle, &total_idle_delta);

    total_combined = (double)(total_user_delta) + (double)(total_user_low_delta) + (double)(total_system_delta);
    total = total_combined + (double)(total_idle_delta);

    if (total == 0) {
        *output = 0;
        return_result = AWS_OP_ERR;
        goto cleanup;
    }

    percent = (total_combined / total) * 100;

    // If negative, there was an error (overflow?)
    if (percent < 0) {
        *output = 0;
        return_result = AWS_OP_ERR;
        goto cleanup;
    }

    *output = percent;
    return_result = AWS_OP_SUCCESS;

cleanup:
    // Cache results
    sampler_linux->cpu_last_total_user = total_user;
    sampler_linux->cpu_last_total_user_low = total_user_low;
    sampler_linux->cpu_last_total_system = total_system;
    sampler_linux->cpu_last_total_idle = total_idle;

    return return_result;
}

static void aws_cpu_sampler_destroy_linux(struct aws_cpu_sampler *sampler) {
    if (sampler == NULL) {
        return;
    }
    struct aws_cpu_sampler_linux *sampler_linux = (struct aws_cpu_sampler_linux *)sampler->impl;
    aws_mem_release(sampler->allocator, sampler_linux);
}

static struct aws_cpu_sampler_vtable aws_cpu_sampler_vtable_linux = {
    .aws_get_cpu_sample_fn = aws_get_cpu_sample_fn_linux,
    .aws_cpu_sampler_destroy = aws_cpu_sampler_destroy_linux,
};

/*********************************************************************************************************************
 * Public operations
 ********************************************************************************************************************/

struct aws_cpu_sampler *aws_cpu_sampler_new(struct aws_allocator *allocator) {
    if (allocator == NULL) {
        aws_raise_error(AWS_ERROR_INVALID_ARGUMENT);
        return NULL;
    }

    struct aws_cpu_sampler_linux *output_linux = aws_mem_calloc(allocator, 1, sizeof(struct aws_cpu_sampler_linux));
    if (output_linux == NULL) {
        return NULL;
    }
    output_linux->base.allocator = allocator;
    output_linux->base.vtable = &aws_cpu_sampler_vtable_linux;
    output_linux->base.impl = output_linux;

    // CPU reporting is done via deltas, so we need to cache the initial CPU values
    double tmp = 0;
    aws_get_cpu_sample_fn_linux(&output_linux->base, &tmp);

    return &output_linux->base;
}
