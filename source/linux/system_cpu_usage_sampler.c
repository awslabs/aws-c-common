/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/common/private/system_cpu_usage_sampler_private.h>
#include <aws/common/system_info.h>

#include <aws/common/logging.h>
#include <aws/common/math.h>

#include <inttypes.h>
#include <sys/sysinfo.h>
#include <sys/types.h>

/*********************************************************************************************************************
 * Linux Specific
 ********************************************************************************************************************/

struct aws_system_cpu_sampler_linux {
    struct aws_system_cpu_sampler base;

    uint64_t cpu_last_total_user;
    uint64_t cpu_last_total_user_low;
    uint64_t cpu_last_total_system;
    uint64_t cpu_last_total_idle;
};

static int s_get_cpu_usage_linux(
    uint64_t *total_user,
    uint64_t *total_user_low,
    uint64_t *total_system,
    uint64_t *total_idle) {

    FILE *file = fopen("/proc/stat", "r");
    if (file == NULL) {
        return aws_raise_error(AWS_ERROR_INVALID_STATE);
    }
    int matched_results = fscanf(
        file,
        "cpu %" SCNu64 " %" SCNu64 " %" SCNu64 " %" SCNu64 "",
        total_user,
        total_user_low,
        total_system,
        total_idle);
    fclose(file);

    if (matched_results == EOF) {
        AWS_LOGF_ERROR(
            AWS_LS_COMMON_GENERAL, "CPU sampler failed to parse /proc/stat. 'cpu' row was not found in file.");
        return aws_raise_error(AWS_ERROR_INVALID_STATE);
    }
    if (matched_results != 4) {
        // There was not 4 CPU results (likely an unsupported platform)
        AWS_LOGF_ERROR(
            AWS_LS_COMMON_GENERAL, "CPU sampler failed to parse /proc/stat. 'cpu' row did not contain 4 rows of data.");
        return aws_raise_error(AWS_ERROR_INVALID_STATE);
    }
    return AWS_OP_SUCCESS;
}

static uint64_t aws_get_cpu_sample_fn_linux_get_uint64_delta(uint64_t first, uint64_t second) {
    uint64_t output = 0;
    if (first > second) {
        aws_sub_u64_checked(first, second, &output);
    } else {
        aws_add_u64_checked((UINT64_MAX - second), first, &output);
    }
    return output;
}

static int aws_get_cpu_sample_fn_linux(struct aws_system_cpu_sampler *sampler, double *output) {
    struct aws_system_cpu_sampler_linux *sampler_linux = sampler->impl;

    // Have to define these here for cleanup
    uint64_t total_user = 0, total_user_low = 0, total_system = 0, total_idle = 0;

    int return_result = s_get_cpu_usage_linux(&total_user, &total_user_low, &total_system, &total_idle);
    if (return_result != AWS_OP_SUCCESS) {
        *output = 0;
        return AWS_OP_ERR;
    }

    uint64_t total_user_delta =
        aws_get_cpu_sample_fn_linux_get_uint64_delta(total_user, sampler_linux->cpu_last_total_user);
    uint64_t total_user_low_delta =
        aws_get_cpu_sample_fn_linux_get_uint64_delta(total_user_low, sampler_linux->cpu_last_total_user_low);
    uint64_t total_system_delta =
        aws_get_cpu_sample_fn_linux_get_uint64_delta(total_system, sampler_linux->cpu_last_total_system);
    uint64_t total_idle_delta =
        aws_get_cpu_sample_fn_linux_get_uint64_delta(total_idle, sampler_linux->cpu_last_total_idle);

    double total_combined = (double)(total_user_delta) + (double)(total_user_low_delta) + (double)(total_system_delta);
    double total = total_combined + (double)(total_idle_delta);

    double percent = 0;
    if (total != 0) {
        percent = (total_combined / total);
    }

    // Clamp to min/max
    if (percent < 0) {
        percent = 0;
    } else if (percent > 1) {
        percent = 1;
    }

    *output = percent;
    // Cache results
    sampler_linux->cpu_last_total_user = total_user;
    sampler_linux->cpu_last_total_user_low = total_user_low;
    sampler_linux->cpu_last_total_system = total_system;
    sampler_linux->cpu_last_total_idle = total_idle;

    return AWS_OP_SUCCESS;
}

static void aws_system_cpu_sampler_destroy_linux(struct aws_system_cpu_sampler *sampler) {
    if (sampler == NULL) {
        return;
    }
    struct aws_system_cpu_sampler_linux *sampler_linux = (struct aws_system_cpu_sampler_linux *)sampler->impl;
    aws_mem_release(sampler->allocator, sampler_linux);
}

static struct aws_system_cpu_sampler_vtable aws_system_cpu_sampler_vtable_linux = {
    .get_sample = aws_get_cpu_sample_fn_linux,
    .destroy = aws_system_cpu_sampler_destroy_linux,
};

/*********************************************************************************************************************
 * Public operations
 ********************************************************************************************************************/

struct aws_system_cpu_sampler *aws_system_cpu_sampler_new(struct aws_allocator *allocator) {
    struct aws_system_cpu_sampler_linux *output_linux =
        aws_mem_calloc(allocator, 1, sizeof(struct aws_system_cpu_sampler_linux));
    output_linux->base.allocator = allocator;
    output_linux->base.vtable = &aws_system_cpu_sampler_vtable_linux;
    output_linux->base.impl = output_linux;

    // CPU reporting is done via deltas, so we need to cache the initial CPU values
    double tmp = 0;
    int sample_return = aws_get_cpu_sample_fn_linux(&output_linux->base, &tmp);

    if (sample_return != AWS_OP_SUCCESS) {
        aws_system_cpu_sampler_destroy(&output_linux->base);
        aws_raise_error(AWS_ERROR_PLATFORM_NOT_SUPPORTED);
        return NULL;
    }

    return &output_linux->base;
}
