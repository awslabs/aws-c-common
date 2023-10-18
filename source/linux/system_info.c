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

static bool s_is_irrelevant_interface(const struct aws_byte_cursor name) {

    /* loop-back is important but not for looking at the system configuration,
      we want the actual cards. */
    struct aws_byte_cursor loopback_cur = aws_byte_cursor_from_c_str("lo");
    if (aws_byte_cursor_starts_with_ignore_case(&name, &loopback_cur)) {
        return true;
    }

    /* typical virtual devices we want to ignore. */
    struct aws_byte_cursor bridge_dev_cur = aws_byte_cursor_from_c_str("br-");
    struct aws_byte_cursor docker_dev_cur = aws_byte_cursor_from_c_str("docker");
    struct aws_byte_cursor virtual_eth_cur = aws_byte_cursor_from_c_str("veth");

    if (aws_byte_cursor_starts_with_ignore_case(&name, &docker_dev_cur) ||
        aws_byte_cursor_starts_with_ignore_case(&name, &virtual_eth_cur) ||
        aws_byte_cursor_starts_with_ignore_case(&name, &bridge_dev_cur)) {
        return true;
    }

    return false;
}

int aws_system_environment_load_platform_impl(struct aws_system_environment *env) {
    /* provide size_hint when reading "special files", since some platforms mis-report these files' size as 4KB */
    aws_byte_buf_init_from_file_with_size_hint(
        &env->virtualization_vendor, env->allocator, "/sys/devices/virtual/dmi/id/sys_vendor", 32 /*size_hint*/);

    /* whether this one works depends on if this is a sysfs filesystem. If it fails, it will just be empty
     * and these APIs are a best effort at the moment. We can add fallbacks as the loaders get more complicated. */
    aws_byte_buf_init_from_file_with_size_hint(
        &env->product_name, env->allocator, "/sys/devices/virtual/dmi/id/product_name", 32 /*size_hint*/);

    /* iterate over network devices. */
    struct ifaddrs *addrs = NULL;
    struct ifaddrs *iterator = NULL;

    getifaddrs(&addrs);
    iterator = addrs;

    while(iterator) {
        if (iterator->ifa_addr && iterator->ifa_addr->sa_family == AF_PACKET) {
            struct aws_string *device_name = aws_string_new_from_c_str(env->allocator, iterator->ifa_name);
            struct aws_byte_cursor device_name_cur = aws_byte_cursor_from_string(device_name);

            if (!s_is_irrelevant_interface(device_name_cur)) {
                /* figure out what numa node if any the network card is on. */
                uint16_t group_id = 0;

                struct aws_byte_buf temp_numa_info;
                aws_byte_buf_init(&temp_numa_info, env->allocator, 256);
                struct aws_byte_cursor initial_path = aws_byte_cursor_from_c_str("/sys/class/net/");
                aws_byte_buf_write_from_whole_cursor(&temp_numa_info, initial_path);
                aws_byte_buf_append_dynamic(&temp_numa_info, &device_name_cur);
                struct aws_byte_cursor final_path_segment = aws_byte_cursor_from_c_str("/device/numa_node");
                aws_byte_buf_append_dynamic(&temp_numa_info, &final_path_segment);
                /* add a null terminator for sys-call land. */
                aws_byte_buf_append_byte_dynamic(&temp_numa_info, 0);

                /* fill in buffer and read it converting to int. */
                struct aws_byte_buf node_file;
                AWS_ZERO_STRUCT(node_file);

                if (aws_byte_buf_init_from_file(&node_file, env->allocator, (const char *)temp_numa_info.buffer) ==
                    AWS_OP_SUCCESS) {
                    struct aws_byte_cursor file_cur = aws_byte_cursor_from_buf(&temp_numa_info);

                    uint64_t parsed_int = 0;
                    if (aws_byte_cursor_utf8_parse_u64(file_cur, &parsed_int) == AWS_OP_SUCCESS) {

                        /* should always be true, but doesn't hurt to be safe. */
                        if (parsed_int < UINT16_MAX) {
                            group_id = (uint16_t)parsed_int;
                        }
                    }
                    aws_byte_buf_clean_up(&node_file);
                }
                aws_byte_buf_clean_up(&temp_numa_info);

                aws_array_list_push_back(&env->str_list_network_cards, &device_name);
                aws_array_list_push_back(&env->u16_nic_to_cpu_group, &group_id);
            }
        }
        iterator = iterator->ifa_next;
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
