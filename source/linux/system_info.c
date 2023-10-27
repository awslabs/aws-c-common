/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */
#include <aws/common/file.h>
#include <aws/common/private/system_info_priv.h>
#include <aws/common/logging.h>

#include <ifaddrs.h>
#include <inttypes.h>
#include <linux/if_packet.h>
#include <net/ethernet.h>
#include <sys/socket.h>
#include <sys/types.h>
#include <inttypes.h>

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

    while (iterator) {
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

uint16_t aws_get_cpu_group_count() {
    struct aws_allocator *allocator = aws_default_allocator();
    struct aws_string *path = aws_string_new_from_c_str(allocator, "/sys/devices/system/node");
    struct aws_directory_iterator *dir_iter = aws_directory_entry_iterator_new(allocator, path);

    if (!dir_iter) {
        return 1U; /* Assuming a single group if unable to open directory */
    }

    uint16_t count = 0;

    do {
        const struct aws_directory_entry *dir_entry = aws_directory_entry_iterator_get_value(dir_iter);
        if (dir_entry) {
            struct aws_byte_cursor search_cur = aws_byte_cursor_from_c_str("/sys/devices/system/node/node");
            struct aws_byte_cursor capture_cur;

            if ((dir_entry->file_type & (AWS_FILE_TYPE_SYM_LINK | AWS_FILE_TYPE_DIRECTORY)) &&
                aws_byte_cursor_find_exact(&dir_entry->relative_path, &search_cur, &capture_cur) == AWS_OP_SUCCESS) {
                AWS_LOGF_TRACE(AWS_LS_COMMON_GENERAL, "static: discovered NUMA node at " PRInSTR "\n", AWS_BYTE_CURSOR_PRI(dir_entry->path));
                count++;
            }

        }
    } while (aws_directory_entry_iterator_next(dir_iter) == AWS_OP_SUCCESS);

    aws_directory_entry_iterator_destroy(dir_iter);
    AWS_LOGF_DEBUG(AWS_LS_COMMON_GENERAL, "static: discovered %" PRIu16 " NUMA nodes on system\n", count);

    return count;
}

static struct aws_string *s_get_path_for_group_cpulist(uint16_t group_idx) {
    struct aws_allocator *allocator = aws_default_allocator();
    struct aws_byte_buf path_buf;
    aws_byte_buf_init(&path_buf, allocator, 256);

    char group_idx_str[6]; /* Enough to hold any 16-bit integer value */
    snprintf(group_idx_str, sizeof(group_idx_str), "%u", group_idx);

    struct aws_byte_cursor initial_path = aws_byte_cursor_from_c_str("/sys/devices/system/node/node");
    struct aws_byte_cursor group_idx_cursor = aws_byte_cursor_from_array(group_idx_str, strlen(group_idx_str));
    struct aws_byte_cursor final_path_segment = aws_byte_cursor_from_c_str("/cpulist");

    aws_byte_buf_append_dynamic(&path_buf, &initial_path);
    aws_byte_buf_append_dynamic(&path_buf, &group_idx_cursor);
    aws_byte_buf_append_dynamic(&path_buf, &final_path_segment);

    struct aws_string *file_path = aws_string_new_from_array(allocator, path_buf.buffer, path_buf.len);
    aws_byte_buf_clean_up(&path_buf);
    return file_path;
}

/** Rather than rely on libnuma which may or not be available on the system, just read the sys files. This assumes a
 * linux /sys hierarchy as follows:
 *
 *  The numa nodes are listed in /sys/devices/system/node/node([\d+]),
 *
 *  Each Node's cpu list is stored in /sys/devices/system/node/node<node index>/cpulist
 *
 *  Whether or not a cpu is a hyper-thread is determined by looking in
 *  sys/devices/system/cpu/cpu<cpu index>/topology/thread_siblings_list. If a value
 *  is present, then it is a hyper-thread.
 */
size_t aws_get_cpu_count_for_group(uint16_t group_idx) {
    size_t cpu_count = 0;
    struct aws_allocator *allocator = aws_default_allocator();
    struct aws_string *file_path = s_get_path_for_group_cpulist(group_idx);

    struct aws_byte_buf file_data;
    if (aws_byte_buf_init_from_file(&file_data, allocator, aws_string_c_str(file_path)) == AWS_OP_SUCCESS) {
        AWS_LOGF_TRACE(AWS_LS_COMMON_GENERAL, "static: discovered cpulist for NUMA node %" PRIu16 " at %s", group_idx, aws_string_c_str(file_path));

        struct aws_array_list cpu_ranges;
        if (aws_array_list_init_dynamic(&cpu_ranges, allocator, 10, sizeof(struct aws_byte_cursor)) == AWS_OP_SUCCESS) {
            struct aws_byte_cursor line_cursor = aws_byte_cursor_from_buf(&file_data);
            struct aws_byte_cursor token;
            AWS_ZERO_STRUCT(token);
            while (aws_byte_cursor_next_split(&line_cursor, ',', &token)) {
                struct aws_byte_cursor trimmed_token = aws_byte_cursor_trim_pred(&token, aws_char_is_space);
                AWS_LOGF_TRACE(AWS_LS_COMMON_GENERAL, "static: Found cpu range " PRInSTR " for node %" PRIu16, AWS_BYTE_CURSOR_PRI(trimmed_token), group_idx);
                aws_array_list_push_back(&cpu_ranges, &trimmed_token);
            }

            size_t range_count = aws_array_list_length(&cpu_ranges);
            for (size_t i = 0; i < range_count; ++i) {
                struct aws_byte_cursor range_cursor;
                aws_array_list_get_at(&cpu_ranges, &range_cursor, i);
                struct aws_byte_cursor start_cursor, end_cursor;
                AWS_ZERO_STRUCT(start_cursor);
                AWS_ZERO_STRUCT(end_cursor);
                if (aws_byte_cursor_next_split(&range_cursor, '-', &start_cursor) &&
                    aws_byte_cursor_next_split(&range_cursor, '-', &end_cursor)) {
                    uint64_t start, end;
                    AWS_LOGF_TRACE(AWS_LS_COMMON_GENERAL, "static: Parsed cpu ranges " PRInSTR "-" PRInSTR " for node %" PRIu16, AWS_BYTE_CURSOR_PRI(start_cursor), AWS_BYTE_CURSOR_PRI(end_cursor), group_idx);
                    if (aws_byte_cursor_utf8_parse_u64(start_cursor, &start) == AWS_OP_SUCCESS &&
                        aws_byte_cursor_utf8_parse_u64(end_cursor, &end) == AWS_OP_SUCCESS) {
                        cpu_count += (size_t)(end - start + 1);
                    }
                } else {
                    uint64_t cpu_id;
                    AWS_LOGF_TRACE(AWS_LS_COMMON_GENERAL, "static: Parsed cpu number " PRInSTR " for node %" PRIu16, AWS_BYTE_CURSOR_PRI(range_cursor), group_idx);

                    if (aws_byte_cursor_utf8_parse_u64(range_cursor, &cpu_id) == AWS_OP_SUCCESS) {
                        cpu_count++;
                    }
                }
            }

            aws_array_list_clean_up(&cpu_ranges);
        }
    } else {
        AWS_LOGF_TRACE(AWS_LS_COMMON_GENERAL, "static: No cpulist for NUMA node %" PRIu16 " found at %s", group_idx, aws_string_c_str(file_path));
    }

    aws_byte_buf_clean_up(&file_data);
    aws_string_destroy(file_path);
    return cpu_count;
}

static bool s_is_cpu_hyperthread(uint32_t cpu_id) {
    struct aws_allocator *allocator = aws_default_allocator();
    bool is_hyperthread = false;

    /* Check for hyper-threading */
    struct aws_byte_buf sibling_path_buf;
    aws_byte_buf_init(&sibling_path_buf, allocator, 256);

    char cpu_id_str[10];
    snprintf(cpu_id_str, sizeof(cpu_id_str), "%" PRIu32, cpu_id);

    struct aws_byte_cursor sibling_initial_path = aws_byte_cursor_from_c_str("/sys/devices/system/cpu/cpu");
    struct aws_byte_cursor sibling_idx_cursor = aws_byte_cursor_from_array(cpu_id_str, strlen(cpu_id_str));
    struct aws_byte_cursor sibling_final_path_segment = aws_byte_cursor_from_c_str("/topology/thread_siblings_list");

    aws_byte_buf_append_dynamic(&sibling_path_buf, &sibling_initial_path);
    aws_byte_buf_append_dynamic(&sibling_path_buf, &sibling_idx_cursor);
    aws_byte_buf_append_dynamic(&sibling_path_buf, &sibling_final_path_segment);

    struct aws_string *sibling_file_path =
        aws_string_new_from_array(allocator, sibling_path_buf.buffer, sibling_path_buf.len);
    aws_byte_buf_clean_up(&sibling_path_buf);

    struct aws_byte_buf sibling_file_data;
    if (aws_byte_buf_init_from_file(&sibling_file_data, allocator, aws_string_c_str(sibling_file_path)) ==
        AWS_OP_SUCCESS) {
        /* If the file is not empty, this CPU is suspected to be part of a hyper-threaded core */
        is_hyperthread = sibling_file_data.len > 1;
        aws_byte_buf_clean_up(&sibling_file_data);
    } else {
        is_hyperthread = false;
    }

    aws_string_destroy(sibling_file_path);
    return is_hyperthread;
}

/** Rather than rely on libnuma which may or not be available on the system, just read the sys files. This assumes a
 * linux /sys hierarchy as follows:
 *
 *  The numa nodes are listed in /sys/devices/system/node/node([\d+]),
 *
 *  Each Node's cpu list is stored in /sys/devices/system/node/node<node index>/cpulist
 *
 *  Whether or not a cpu is a hyper-thread is determined by looking in
 *  sys/devices/system/cpu/cpu<cpu index>/topology/thread_siblings_list. If a value
 *  is present, then it is a hyper-thread.
 */
void aws_get_cpu_ids_for_group(uint16_t group_idx, struct aws_cpu_info *cpu_ids_array, size_t cpu_ids_array_length) {
    struct aws_allocator *allocator = aws_default_allocator();
    struct aws_string *file_path = s_get_path_for_group_cpulist(group_idx);

    /* Read the CPU list from the file */
    struct aws_byte_buf file_data;
    if (aws_byte_buf_init_from_file(&file_data, allocator, aws_string_c_str(file_path)) == AWS_OP_SUCCESS) {
        AWS_LOGF_TRACE(AWS_LS_COMMON_GENERAL, "static: discovered cpulist for NUMA node %" PRIu16 " at %s", group_idx, aws_string_c_str(file_path));
        /* Parse the CPU list */
        struct aws_array_list cpu_ranges;
        AWS_FATAL_ASSERT(
            aws_array_list_init_dynamic(&cpu_ranges, allocator, 10, sizeof(struct aws_byte_cursor)) == AWS_OP_SUCCESS);

        struct aws_byte_cursor line_cursor = aws_byte_cursor_from_buf(&file_data);
        struct aws_byte_cursor token;
        AWS_ZERO_STRUCT(token);
        while (aws_byte_cursor_next_split(&line_cursor, ',', &token)) {
            struct aws_byte_cursor trimmed_token = aws_byte_cursor_trim_pred(&token, aws_char_is_space);
            AWS_LOGF_TRACE(AWS_LS_COMMON_GENERAL, "static: Found cpu range " PRInSTR " for node %" PRIu16, AWS_BYTE_CURSOR_PRI(trimmed_token), group_idx);
            aws_array_list_push_back(&cpu_ranges, &trimmed_token);
        }

        /* Iterate over the CPU ranges and fill in the cpu_ids_array */
        size_t cpu_count = 0;
        size_t range_count = aws_array_list_length(&cpu_ranges);
        for (size_t i = 0; i < range_count; ++i) {
            struct aws_byte_cursor range_cursor;
            aws_array_list_get_at(&cpu_ranges, &range_cursor, i);
            struct aws_byte_cursor start_cursor, end_cursor;
            AWS_ZERO_STRUCT(start_cursor);
            AWS_ZERO_STRUCT(end_cursor);
            if (aws_byte_cursor_next_split(&range_cursor, '-', &start_cursor) &&
                aws_byte_cursor_next_split(&range_cursor, '-', &end_cursor)) {
                uint64_t start, end;
                if (aws_byte_cursor_utf8_parse_u64(start_cursor, &start) == AWS_OP_SUCCESS &&
                    aws_byte_cursor_utf8_parse_u64(end_cursor, &end) == AWS_OP_SUCCESS) {
                    AWS_LOGF_TRACE(AWS_LS_COMMON_GENERAL, "static: Parsed cpu ranges " PRInSTR "-" PRInSTR " for node %" PRIu16, AWS_BYTE_CURSOR_PRI(start_cursor), AWS_BYTE_CURSOR_PRI(end_cursor), group_idx);
                    for (uint64_t j = start; j <= end && cpu_count < cpu_ids_array_length; ++j) {
                        cpu_ids_array[cpu_count].cpu_id = (int32_t)j;
                        cpu_ids_array[cpu_count].suspected_hyper_thread = s_is_cpu_hyperthread((uint32_t)j);
                        AWS_LOGF_TRACE(AWS_LS_COMMON_GENERAL, "static: cpu %" PRId32 " is hyper-thread? %s", cpu_ids_array[cpu_count].cpu_id, cpu_ids_array[cpu_count].suspected_hyper_thread ? "true": "false");
                        cpu_count++;
                    }
                }
            } else {
                uint64_t cpu_id;
                AWS_LOGF_TRACE(AWS_LS_COMMON_GENERAL, "static: Parsed cpu number " PRInSTR " for node %" PRIu16, AWS_BYTE_CURSOR_PRI(range_cursor), group_idx);
                if (aws_byte_cursor_utf8_parse_u64(range_cursor, &cpu_id) == AWS_OP_SUCCESS &&
                    cpu_count < cpu_ids_array_length) {
                    cpu_ids_array[cpu_count].cpu_id = (int32_t)cpu_id;
                    cpu_ids_array[cpu_count].suspected_hyper_thread = s_is_cpu_hyperthread((uint32_t)cpu_id);
                    AWS_LOGF_TRACE(AWS_LS_COMMON_GENERAL, "static: cpu %" PRId32 " is hyper-thread? %s", cpu_ids_array[cpu_count].cpu_id, cpu_ids_array[cpu_count].suspected_hyper_thread ? "true": "false");
                    cpu_count++;
                }
            }
        }

        aws_array_list_clean_up(&cpu_ranges);
    } else {
        AWS_LOGF_TRACE(AWS_LS_COMMON_GENERAL, "static: No cpulist for NUMA node %" PRIu16 " found at %s", group_idx, aws_string_c_str(file_path));
    }
    aws_string_destroy(file_path);
    aws_byte_buf_clean_up(&file_data);
}
