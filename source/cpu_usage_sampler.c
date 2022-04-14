/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/common/cpu_usage_sampler.h>

#if defined(__linux__) || defined(__unix__)
#    include <sys/sysinfo.h>
#    include <sys/types.h>
#endif

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

static void aws_cpu_sampler_destroy_default(struct aws_cpu_sampler *sampler) {
    if (sampler == NULL) {
        return;
    }
    aws_mem_release(sampler->allocator, sampler);
}

static struct aws_cpu_sampler_vtable aws_cpu_sampler_vtable_default = {
    .aws_get_cpu_sample_fn = NULL,
    .aws_cpu_sampler_destroy = aws_cpu_sampler_destroy_default,
};

/*********************************************************************************************************************
 * Linux
 ********************************************************************************************************************/

#if defined(__linux__) || defined(__unix__)

struct aws_cpu_sampler_linux {
    struct aws_cpu_sampler base;
    
    uint64_t cpu_last_total_user;
    uint64_t cpu_last_total_user_low;
    uint64_t cpu_last_total_system;
    uint64_t cpu_last_total_idle;
    // CPU usage is reported in deltas on Linux.
    // For the first report we have to process and cache but not send.
    bool cpu_only_gather;
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

static int aws_get_cpu_sample_fn_linux(struct aws_cpu_sampler *sampler, double *output) {
    struct aws_cpu_sampler_linux *sampler_linux = sampler->impl;

    int return_result = AWS_OP_ERR;
    uint64_t total_user, total_user_low, total_system, total_idle, total;
    s_get_cpu_usage_linux(&total_user, &total_user_low, &total_system, &total_idle);
    // total_combined needs to be double to allow for fractions
    double percent, total_combined;

    // If the value has overflown and wrapped around, swap the variables
    uint64_t tmp;
    if (total_user < sampler_linux->cpu_last_total_user) {
        tmp = total_user;
        total_user = sampler_linux->cpu_last_total_user;
        sampler_linux->cpu_last_total_user = tmp;
    }
    if (total_user_low < sampler_linux->cpu_last_total_user_low) {
        tmp = total_user_low;
        total_user_low = sampler_linux->cpu_last_total_user_low;
        sampler_linux->cpu_last_total_user_low = tmp;
    }
    if (total_system < sampler_linux->cpu_last_total_system) {
        tmp = total_system;
        total_system = sampler_linux->cpu_last_total_system;
        sampler_linux->cpu_last_total_system = tmp;
    }
    if (total_idle < sampler_linux->cpu_last_total_idle) {
        tmp = total_idle;
        total_idle = sampler_linux->cpu_last_total_idle;
        sampler_linux->cpu_last_total_idle = tmp;
    }

    uint64_t total_user_delta, total_user_low_delta, total_system_delta, total_idle_delta;
    if (aws_sub_u64_checked(total_user, sampler_linux->cpu_last_total_user, &total_user_delta) != AWS_OP_SUCCESS) {
        *output = 0;
        return_result = AWS_OP_ERR;
        goto cleanup;
    }
    if (aws_sub_u64_checked(total_user_low, sampler_linux->cpu_last_total_user_low, &total_user_low_delta) !=
        AWS_OP_SUCCESS) {
        *output = 0;
        return_result = AWS_OP_ERR;
        goto cleanup;
    }
    if (aws_sub_u64_checked(total_system, sampler_linux->cpu_last_total_system, &total_system_delta) !=
        AWS_OP_SUCCESS) {
        *output = 0;
        return_result = AWS_OP_ERR;
        goto cleanup;
    }
    if (aws_sub_u64_checked(total_idle, sampler_linux->cpu_last_total_idle, &total_idle_delta) != AWS_OP_SUCCESS) {
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

    if (sampler_linux->cpu_only_gather == false) {
        *output = percent;
        return_result = AWS_OP_SUCCESS;
    } else {
        return_result = AWS_OP_ERR; // will tell DeviceDefender not to send
    }

cleanup:
    // Cache results
    sampler_linux->cpu_last_total_user = total_user;
    sampler_linux->cpu_last_total_user_low = total_user_low;
    sampler_linux->cpu_last_total_system = total_system;
    sampler_linux->cpu_last_total_idle = total_idle;
    sampler_linux->cpu_only_gather = false;

    return return_result;
}

static void aws_cpu_sampler_destroy_linux(struct aws_cpu_sampler *sampler) {
    if (sampler == NULL) {
        return;
    }
    struct aws_cpu_sampler_linux *sampler_linux = (struct aws_cpu_sampler_linux*)sampler->impl;
    aws_mem_release(sampler->allocator, sampler_linux);
}

static struct aws_cpu_sampler_vtable aws_cpu_sampler_vtable_linux = {
    .aws_get_cpu_sample_fn = aws_get_cpu_sample_fn_linux,
    .aws_cpu_sampler_destroy = aws_cpu_sampler_destroy_linux,
};

#endif // Linux

/*********************************************************************************************************************
 * Public operations
 ********************************************************************************************************************/

struct aws_cpu_sampler *aws_cpu_sampler_new(struct aws_allocator *allocator) {
    if (allocator == NULL) {
        aws_raise_error(AWS_ERROR_INVALID_ARGUMENT);
        return NULL;
    }

    // Linux
#if defined(__linux__) || defined(__unix__)
    struct aws_cpu_sampler_linux *output_linux = aws_mem_calloc(allocator, 1, sizeof(struct aws_cpu_sampler_linux));
    if (output_linux == NULL) {
        return NULL;
    }
    output_linux->base.allocator = allocator;
    output_linux->base.vtable = &aws_cpu_sampler_vtable_linux;
    output_linux->base.impl = output_linux;
    output_linux->cpu_only_gather = true;
    return &output_linux->base;
#endif

    // OS not supported
    struct aws_cpu_sampler *output_unsupported = aws_mem_calloc(allocator, 1, sizeof(struct aws_cpu_sampler));
    output_unsupported->allocator = allocator;
    output_unsupported->impl = NULL;
    output_unsupported->vtable = &aws_cpu_sampler_vtable_default;
    return output_unsupported;
}

void aws_cpu_sampler_clean_up(struct aws_cpu_sampler *sampler) {
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
