/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/common/cpu_usage_sampler.h>

int aws_cpu_sampler_new(struct aws_allocator *allocator, struct cpu_usage_sampler *sampler)
{
    // Return the correct platform-specific sampler only if we're passed NULL
    if (sampler != NULL) {
        aws_raise_error(AWS_ERROR_INVALID_ARGUMENT);
        return AWS_OP_ERR;
    }

    // Linux
#if defined(__linux__) || defined(__unix__)
    sampler = aws_mem_acquire(allocator, sizeof(struct cpu_usage_sampler_linux));
    sampler->allocator = allocator;
    return AWS_OP_SUCCESS;
#endif

    // Not supported? return null and aws_op_err
    sampler = NULL;
    return AWS_OP_ERR;
}

void aws_cpu_sampler_cleanup(struct cpu_usage_sampler *sampler)
{
    if (sampler != NULL) {
        aws_mem_release(sampler->allocator, sampler);
    }
}

int aws_cpu_sampler_get_sample(struct cpu_usage_sampler *sampler, double *output)
{
    if (sampler != NULL) {
        aws_raise_error(AWS_ERROR_INVALID_ARGUMENT);
        return AWS_OP_ERR;
    }

    // Linux
#if defined(__linux__) || defined(__unix__)
    struct cpu_usage_sampler_linux *sampler_linux = (struct cpu_usage_sampler_linux*)sampler;
    return sample_usage_linux(sampler_linux, output);
#endif

    // Not supported? return AWS_OP_ERR
    aws_raise_error(AWS_ERROR_PLATFORM_NOT_SUPPORTED);
    return AWS_OP_ERR;
}


// Linux specific functions
#if defined(__linux__) || defined(__unix__)

static void s_get_cpu_usage(
    uint64_t *total_user,
    uint64_t *total_user_low,
    uint64_t *total_system,
    uint64_t *total_idle) {

    FILE *file;
    int matched_results;
    file = fopen("/proc/stat", "r");
    matched_results = fscanf(
        file,
        "cpu %llu %llu %llu %llu",
        (long long unsigned int *)total_user,
        (long long unsigned int *)total_user_low,
        (long long unsigned int *)total_system,
        (long long unsigned int *)total_idle);
    fclose(file);
    if (matched_results == EOF || matched_results != 4) {
        aws_raise_error(AWS_ERROR_INVALID_STATE);
    }
}

const int sample_usage_linux(struct cpu_usage_sampler_linux *sampler, double *output)
{
    int return_result = AWS_OP_ERR;
    uint64_t total_user, total_user_low, total_system, total_idle, total;
    s_get_cpu_usage(&total_user, &total_user_low, &total_system, &total_idle);
    // total_combined needs to be double to allow for fractions
    double percent, total_combined;

    // If the value has overflown and wrapped around, swap the variables
    uint64_t tmp;
    if (total_user < *sampler->cpu_last_total_user) {
        tmp = total_user;
        total_user = *sampler->cpu_last_total_user;
        *sampler->cpu_last_total_user = tmp;
    }
    if (total_user_low < *sampler->cpu_last_total_user_low) {
        tmp = total_user_low;
        total_user_low = *sampler->cpu_last_total_user_low;
        *sampler->cpu_last_total_user_low = tmp;
    }
    if (total_system < *sampler->cpu_last_total_system) {
        tmp = total_system;
        total_system = *sampler->cpu_last_total_system;
        *sampler->cpu_last_total_system = tmp;
    }
    if (total_idle < *sampler->cpu_last_total_idle) {
        tmp = total_idle;
        total_idle = *sampler->cpu_last_total_idle;
        *sampler->cpu_last_total_idle = tmp;
    }

    uint64_t total_user_delta, total_user_low_delta, total_system_delta, total_idle_delta;
    if (aws_sub_u64_checked(total_user, *sampler->cpu_last_total_user, &total_user_delta) != AWS_OP_SUCCESS) {
        *output = 0;
        return_result = AWS_OP_ERR;
        goto cleanup;
    }
    if (aws_sub_u64_checked(total_user_low, *sampler->cpu_last_total_user_low, &total_user_low_delta) != AWS_OP_SUCCESS) {
        *output = 0;
        return_result = AWS_OP_ERR;
        goto cleanup;
    }
    if (aws_sub_u64_checked(total_system, *sampler->cpu_last_total_system, &total_system_delta) != AWS_OP_SUCCESS) {
        *output = 0;
        return_result = AWS_OP_ERR;
        goto cleanup;
    }
    if (aws_sub_u64_checked(total_idle, *sampler->cpu_last_total_idle, &total_idle_delta) != AWS_OP_SUCCESS) {
        *output = 0;
        return_result = AWS_OP_ERR;
        goto cleanup;
    }

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

    *output = percent;

cleanup:
    // Cache results
    *sampler->cpu_last_total_user = total_user;
    *sampler->cpu_last_total_user_low = total_user_low;
    *sampler->cpu_last_total_system = total_system;
    *sampler->cpu_last_total_idle = total_idle;

    return return_result;
}
#endif // end of Linux specific functions
