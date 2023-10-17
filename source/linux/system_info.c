/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */
#include <aws/common/file.h>
#include <aws/common/private/system_info_priv.h>

#include <ifaddrs.h>
#include <sys/types.h>
#include <sys/socket.h>
#include <linux/if_packet.h>
#include <net/ethernet.h>

int aws_system_environment_load_platform_impl(struct aws_system_environment *env) {
    /* provide size_hint when reading "special files", since some platforms mis-report these files' size as 4KB */
    aws_byte_buf_init_from_file_with_size_hint(
        &env->virtualization_vendor, env->allocator, "/sys/devices/virtual/dmi/id/sys_vendor", 32 /*size_hint*/);

    /* whether this one works depends on if this is a sysfs filesystem. If it fails, it will just be empty
     * and these APIs are a best effort at the moment. We can add fallbacks as the loaders get more complicated. */
    aws_byte_buf_init_from_file_with_size_hint(
        &env->product_name, env->allocator, "/sys/devices/virtual/dmi/id/product_name", 32 /*size_hint*/);

    struct ifaddrs *addrs;
    struct ifaddrs *iterator;
    iterator = addrs;

    getifaddrs(&addrs);

    while(iterator) {
        if (iterator->ifa_addr && iterator->ifa_addr->sa_family == AF_PACKET) {
            struct aws_string *device_name = aws_string_new_from_c_str(env->allocator, iterator->ifa_name);
            aws_array_list_push_back(&env->str_list_network_cards, &device_name);
        }
    }

    if (addrs) {
        freeifaddrs(addrs);
    }

    return AWS_OP_SUCCESS;
}

void aws_system_environment_destroy_platform_impl(struct aws_system_environment *env) {
    size_t length = aws_array_list_length(&env->str_list_network_cards);

    for (size_t i = 0; i < length; ++i) {
        struct aws_string *device_name = NULL;
        aws_array_list_get_at(&env->str_list_network_cards, &device_name, i);
        aws_string_destroy(device_name);
    }

    aws_byte_buf_clean_up(&env->virtualization_vendor);
    aws_byte_buf_clean_up(&env->product_name);
}
