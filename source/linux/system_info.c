/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */
#include <aws/common/file.h>
#include <aws/common/private/system_info_priv.h>

int aws_system_environment_load_platform_impl(struct aws_system_environment *env) {
    aws_byte_buf_init_from_file(&env->virtualization_vendor, env->allocator, "/sys/devices/virtual/dmi/id/sys_vendor");
    /* whether this one works depends on if this is a sysfs filesystem. If it fails, it will just be empty
     * and these APIs are a best effort at the moment. We can add fallbacks as the loaders get more complicated. */
    aws_byte_buf_init_from_file(&env->product_name, env->allocator, "/sys/devices/virtual/dmi/id/product_name");

    return AWS_OP_SUCCESS;
}

void aws_system_environment_destroy_platform_impl(struct aws_system_environment *env) {
    aws_byte_buf_clean_up(&env->virtualization_vendor);
    aws_byte_buf_clean_up(&env->product_name);
}
