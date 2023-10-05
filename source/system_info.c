/**
* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
* SPDX-License-Identifier: Apache-2.0.
*/
#include <aws/common/private/system_info_priv.h>

struct aws_system_environment *aws_system_environment_load(struct aws_allocator *allocator) {
    struct aws_system_environment *env = aws_mem_calloc(allocator, 1, sizeof(struct aws_system_environment));
    env->allocator = allocator;

    if (aws_system_environment_load_platform_impl(env)) {
        goto error;
    }

    aws_system_environment_load_virtualization_vendor_impl(env);
    env->os = aws_get_platform_build_os();
    env->cpu_count = aws_system_info_processor_count();
    env->cpu_group_count = aws_get_cpu_group_count();

    return env;
error:
    aws_mem_release(allocator, env);

    return NULL;
}

void aws_system_environment_destroy(struct aws_system_environment *env) {
    if (env) {
        aws_system_environment_destroy_platform_impl(env);
        aws_mem_release(env->allocator, env);
    }

}

struct aws_byte_cursor aws_system_environment_get_virtualization_vendor(struct aws_system_environment *env) {
    return aws_byte_cursor_from_buf(&env->virtualization_vendor);
}

size_t aws_system_environment_get_processor_count(struct aws_system_environment *env) {
    return env->cpu_count;
}

AWS_COMMON_API
size_t aws_system_environment_get_cpu_group_count(struct aws_system_environment *env) {
    return env->cpu_group_count;
}
