/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */
#include <aws/common/private/system_info_priv.h>

#include <aws/common/logging.h>

void s_destroy_env(void *arg) {
    struct aws_system_environment *env = arg;

    if (env) {
        aws_system_environment_destroy_platform_impl(env);
        aws_mem_release(env->allocator, env);
    }
}

struct aws_system_environment *aws_system_environment_load(struct aws_allocator *allocator) {
    struct aws_system_environment *env = aws_mem_calloc(allocator, 1, sizeof(struct aws_system_environment));
    env->allocator = allocator;
    aws_ref_count_init(&env->ref_count, env, s_destroy_env);

    if (aws_system_environment_load_platform_impl(env)) {
        AWS_LOGF_ERROR(
            AWS_LS_COMMON_GENERAL,
            "id=%p: failed to load system environment with error %s.",
            (void *)env,
            aws_error_debug_str(aws_last_error()));
        goto error;
    }

    AWS_LOGF_TRACE(
        AWS_LS_COMMON_GENERAL,
        "id=%p: virtualization vendor detected as \"" PRInSTR "\"",
        (void *)env,
        AWS_BYTE_CURSOR_PRI(aws_system_environment_get_virtualization_vendor(env)));
    AWS_LOGF_TRACE(
        AWS_LS_COMMON_GENERAL,
        "id=%p: virtualization product name detected as \"" PRInSTR " \"",
        (void *)env,
        AWS_BYTE_CURSOR_PRI(aws_system_environment_get_virtualization_vendor(env)));

    env->os = aws_get_platform_build_os();
    env->cpu_count = aws_system_info_processor_count();
    env->cpu_group_count = aws_get_cpu_group_count();

    return env;
error:
    s_destroy_env(env);
    return NULL;
}

struct aws_system_environment *aws_system_environment_acquire(struct aws_system_environment *env) {
    aws_ref_count_acquire(&env->ref_count);
    return env;
}

void aws_system_environment_release(struct aws_system_environment *env) {
    aws_ref_count_release(&env->ref_count);
}

struct aws_byte_cursor aws_system_environment_get_virtualization_vendor(const struct aws_system_environment *env) {
    struct aws_byte_cursor vendor_string = aws_byte_cursor_from_buf(&env->virtualization_vendor);
    return aws_byte_cursor_trim_pred(&vendor_string, aws_char_is_space);
}

struct aws_byte_cursor aws_system_environment_get_virtualization_product_name(
    const struct aws_system_environment *env) {
    struct aws_byte_cursor product_name_str = aws_byte_cursor_from_buf(&env->product_name);
    return aws_byte_cursor_trim_pred(&product_name_str, aws_char_is_space);
}

size_t aws_system_environment_get_processor_count(struct aws_system_environment *env) {
    return env->cpu_count;
}

AWS_COMMON_API
size_t aws_system_environment_get_cpu_group_count(const struct aws_system_environment *env) {
    return env->cpu_group_count;
}

static uint8_t s_platform_string_buffer[32];
static struct aws_byte_buf s_platform_buf =
    {.buffer = s_platform_string_buffer, .capacity = sizeof(s_platform_string_buffer), .len = 0, .allocator = NULL};

struct aws_byte_cursor aws_get_platform_build_os_string(void) {
    if (s_platform_buf.len != 0) {
        return aws_byte_cursor_from_buf(&s_platform_buf);
    }

    enum aws_platform_os os = aws_get_platform_build_os();
    struct aws_byte_cursor os_str;
    struct aws_byte_cursor arch_str;

    switch (os) {
        case AWS_PLATFORM_OS_WINDOWS:
            os_str = aws_byte_cursor_from_c_str("Windows");
            break;
        case AWS_PLATFORM_OS_MAC:
            os_str = aws_byte_cursor_from_c_str("macOS");
            break;
        case AWS_PLATFORM_OS_IOS:
            os_str = aws_byte_cursor_from_c_str("iOS");
            break;
        case AWS_PLATFORM_OS_TVOS:
            os_str = aws_byte_cursor_from_c_str("tvOS");
            break;
        case AWS_PLATFORM_OS_WATCHOS:
            os_str = aws_byte_cursor_from_c_str("watchOS");
            break;
        case AWS_PLATFORM_OS_ANDROID:
            os_str = aws_byte_cursor_from_c_str("Android");
            break;
        case AWS_PLATFORM_OS_BSD:
            os_str = aws_byte_cursor_from_c_str("BSD");
            break;
        case AWS_PLATFORM_OS_UNIX:
            os_str = aws_byte_cursor_from_c_str("Unix");
            break;
        default:
            os_str = aws_byte_cursor_from_c_str("unknown");
            AWS_LOGF_WARN(AWS_LS_COMMON_GENERAL, "Unknown platform OS enum value: %d", (int)os);
    }

#ifdef AWS_ARCH_INTEL
    arch_str = aws_byte_cursor_from_c_str("intel");
#elif defined(AWS_ARCH_INTEL_64)
    arch_str = aws_byte_cursor_from_c_str("intel64");
#elif defined(AWS_ARCH_ARM64)
    arch_str = aws_byte_cursor_from_c_str("arm64");
#elif defined(AWS_ARCH_ARM32)
    arch_str = aws_byte_cursor_from_c_str("arm32");
#else
    arch_str = aws_byte_cursor_from_c_str("unknown");
    AWS_LOGF_WARN(AWS_LS_COMMON_GENERAL, "Unknown platform architecture.");
#endif

    aws_byte_buf_reset(&s_platform_buf, false);
    aws_byte_buf_append(&s_platform_buf, &os_str);
    const struct aws_byte_cursor s_dash = aws_byte_cursor_from_c_str("-");
    aws_byte_buf_append(&s_platform_buf, &s_dash);
    aws_byte_buf_append(&s_platform_buf, &arch_str);

    return aws_byte_cursor_from_buf(&s_platform_buf);
}
