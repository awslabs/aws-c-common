#ifndef AWS_COMMON_SYSTEM_INFO_PRIV_H
#define AWS_COMMON_SYSTEM_INFO_PRIV_H
/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/common/system_info.h>
#include <aws/common/byte_buf.h>
#include <aws/common/string.h>

struct aws_system_environment {
    struct aws_allocator *allocator;
    struct aws_byte_buf virtualization_vendor;
    struct aws_byte_buf product_name;
    enum aws_platform_os os;
    size_t cpu_count;
    size_t cpu_group_count;
    void *additional_impl_data;
};

int aws_system_environment_load_platform_impl(struct aws_system_environment *env);
void aws_system_environment_destroy_platform_impl(struct aws_system_environment *env);

#endif /* AWS_COMMON_SYSTEM_INFO_PRIV_H */
