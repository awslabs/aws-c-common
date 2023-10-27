/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */
#include <aws/common/private/system_info_priv.h>

#include <aws/common/logging.h>

int aws_system_environment_load_platform_impl(struct aws_system_environment *env) {
    (void)env;
    AWS_LOGF_DEBUG(
        AWS_LS_COMMON_GENERAL,
        "id=%p: platform specific environment loading is not implemented for this platform.",
        (void *)env);

    return AWS_OP_SUCCESS;
}

void aws_system_environment_destroy_platform_impl(struct aws_system_environment *env) {
    (void)env;
}

uint16_t aws_get_cpu_group_count(void) {
    /* if we're here we have no idea how to get NUMA info. Assume 1 as that's most likely the case anyways. */
    return 1U;
}

size_t aws_get_cpu_count_for_group(uint16_t group_idx) {
    (void)group_idx;
    /* if we're here we have no idea how to get NUMA info. Assume 1 group and return all cpus on the system. */
    return aws_system_info_processor_count();
}

void aws_get_cpu_ids_for_group(uint16_t group_idx, struct aws_cpu_info *cpu_ids_array, size_t cpu_ids_array_length) {
    (void)group_idx;
    AWS_PRECONDITION(cpu_ids_array);

    if (!cpu_ids_array_length) {
        return;
    }

    /* if we're here we have no idea how to get NUMA info. Assume 1 group and use all the cpus passed. */
    /* go ahead and initialize everything. */
    for (size_t i = 0; i < cpu_ids_array_length; ++i) {
        cpu_ids_array[i].cpu_id = -1;
        cpu_ids_array[i].suspected_hyper_thread = false;
    }

    /* a crude hint, but hyper-threads are numbered as the second half of the cpu id listing. The assumption if you
     * hit here is that this is just listing all cpus on the system. */
    size_t hyper_thread_hint = cpu_ids_array_length / 2 - 1;

    for (size_t i = 0; i < cpu_ids_array_length; ++i) {
        cpu_ids_array[i].cpu_id = (int32_t)i;
        cpu_ids_array[i].suspected_hyper_thread = i > hyper_thread_hint;
    }
}
