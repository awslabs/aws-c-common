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
    aws_system_environment_load_virtualization_product_name_impl(env);

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
    struct aws_byte_cursor vendor_string = aws_byte_cursor_from_buf(&env->virtualization_vendor);
    return aws_byte_cursor_trim_pred(&vendor_string, aws_char_is_space);
}

struct aws_byte_cursor aws_system_environment_get_virtualization_product_name(struct aws_system_environment *env) {
    struct aws_byte_cursor product_name_str = aws_byte_cursor_from_buf(&env->product_name);
    return aws_byte_cursor_trim_pred(&product_name_str, aws_char_is_space);
}

size_t aws_system_environment_get_processor_count(struct aws_system_environment *env) {
    return env->cpu_count;
}

AWS_COMMON_API
size_t aws_system_environment_get_cpu_group_count(struct aws_system_environment *env) {
    return env->cpu_group_count;
}
