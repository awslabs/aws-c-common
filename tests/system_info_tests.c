/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/common/system_info.h>

#include "logging/test_logger.h"
#include <aws/testing/aws_test_harness.h>

static int s_test_cpu_count_at_least_works_superficially_fn(struct aws_allocator *allocator, void *ctx) {
    (void)allocator;
    (void)ctx;

    size_t processor_count = aws_system_info_processor_count();
    /* I think this is a fairly reasonable assumption given the circumstances
     * (you know this test is part of a program
     * that must be running on at least one core).... */
    ASSERT_TRUE(processor_count > 0);

    return 0;
}

AWS_TEST_CASE(test_cpu_count_at_least_works_superficially, s_test_cpu_count_at_least_works_superficially_fn)

#if defined(_WIN32)
#    include <io.h>
#    define DIRSEP "\\"
#else
#    define DIRSEP "/"
#endif

static int s_test_stack_trace_decoding(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;

    struct aws_logger test_log;
    test_logger_init(&test_log, allocator, AWS_LL_TRACE, 0);
    aws_logger_set(&test_log);

    int line = 0; /* captured on line of aws_backtrace_log call to match call site */
    (void)line;   /* may not be used if debug info is unavailable */
    aws_backtrace_log(AWS_LL_TRACE), (line = __LINE__); /* NOLINT */

    struct test_logger_impl *log = test_log.p_impl;
    ASSERT_NOT_NULL(log);

    struct aws_byte_buf *buffer = &log->log_buffer;
    (void)buffer;

#if defined(AWS_BACKTRACE_STACKS_AVAILABLE) && defined(DEBUG_BUILD)
    /* ensure that this file/function is found */
    char *file = __FILE__;
    char *next = strstr(file, DIRSEP);
    /* strip path info, just filename will be found */
    while (next) {
        file = next + 1;
        next = strstr(file, DIRSEP);
    }

    struct aws_byte_cursor null_term = aws_byte_cursor_from_array("", 1);
    aws_byte_buf_append_dynamic(buffer, &null_term);
    fprintf(stderr, "%s", (const char *)buffer->buffer);
    const char *func = __func__;
    if (func[0] == 's' && func[1] == '_') {
        func += 2; /* skip over s_ */
    }
    ASSERT_NOT_NULL(strstr((const char *)buffer->buffer, func));
    /* if this is not a debug build, there may not be symbols, so the test cannot
     * verify if a best effort was made */
    if (strstr((const char *)buffer->buffer, file)) {
        /* check for the call site of aws_backtrace_print. Note that line numbers are off by one
         * in both directions depending on compiler, so we check a range around the call site __LINE__
         * The line number can also be ? on old compilers
         */
        char fileline[4096];
        uint32_t found_file_line = 0;
        for (int lineno = line - 1; lineno <= line + 1; ++lineno) {
            snprintf(fileline, sizeof(fileline), "%s:%d", file, lineno);
            found_file_line = strstr((const char *)buffer->buffer, fileline) != NULL;
            if (found_file_line) {
                break;
            }
        }
        if (!found_file_line) {
            snprintf(fileline, sizeof(fileline), "%s:?", file);
            found_file_line = strstr((const char *)buffer->buffer, fileline) != NULL;
        }

        ASSERT_TRUE(found_file_line);
    }
#endif

    aws_logger_clean_up(&test_log);
    return 0;
}

AWS_TEST_CASE(test_stack_trace_decoding, s_test_stack_trace_decoding);

static int s_test_platform_build_os_fn(struct aws_allocator *allocator, void *ctx) {
    (void)allocator;
    (void)ctx;

    enum aws_platform_os build_os = aws_get_platform_build_os();

#if defined(AWS_OS_APPLE)
    ASSERT_INT_EQUALS(build_os, AWS_PLATFORM_OS_MAC);
#elif defined(_WIN32)
    ASSERT_INT_EQUALS(build_os, AWS_PLATFORM_OS_WINDOWS);
#else
    ASSERT_INT_EQUALS(build_os, AWS_PLATFORM_OS_UNIX);
#endif

    return 0;
}

AWS_TEST_CASE(test_platform_build_os, s_test_platform_build_os_fn)

static int s_test_sanity_check_numa_discovery(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;

    aws_common_library_init(allocator);
    size_t processor_count = aws_system_info_processor_count();
    ASSERT_TRUE(processor_count > 0);

    uint16_t group_count = aws_get_cpu_group_count();
    ASSERT_TRUE(group_count > 0);

    /* log for the test output since it's the only way I can verify on certain platforms this looks correct. */
    AWS_LOGF_INFO(AWS_LS_COMMON_GENERAL, "found %d cpu groups", (int)group_count);

    size_t total_cpus_found_via_numa = 0;
    for (uint16_t i = 0; i < group_count; ++i) {
        size_t cpus_per_group = aws_get_cpu_count_for_group(i);
        AWS_LOGF_INFO(
            AWS_LS_COMMON_GENERAL, "found cpu count %d, which lives on group node %d", (int)cpus_per_group, (int)i);

        ASSERT_TRUE(cpus_per_group > 0);
        total_cpus_found_via_numa += cpus_per_group;

        struct aws_cpu_info *cpus_for_group = aws_mem_calloc(allocator, cpus_per_group, sizeof(struct aws_cpu_info));
        ASSERT_NOT_NULL(cpus_per_group);
        aws_get_cpu_ids_for_group(i, cpus_for_group, cpus_per_group);

        /* make sure at least one is set */
        bool at_least_one = false;
        for (size_t cpu_idx = 0; cpu_idx < cpus_per_group; ++cpu_idx) {
            AWS_LOGF_INFO(
                AWS_LS_COMMON_GENERAL,
                "found cpu_id %d, which lives on group node %d. Is it likely a hyper-thread ? %s",
                (int)cpus_for_group[cpu_idx].cpu_id,
                (int)i,
                cpus_for_group[cpu_idx].suspected_hyper_thread ? "Yes" : "No");
            if (cpus_for_group[cpu_idx].cpu_id >= 0) {
                at_least_one = true;
            }
        }

        ASSERT_TRUE(at_least_one);
        aws_mem_release(allocator, cpus_for_group);
    }

    ASSERT_TRUE(total_cpus_found_via_numa <= processor_count);

    aws_common_library_clean_up();
    return 0;
}

AWS_TEST_CASE(test_sanity_check_numa_discovery, s_test_sanity_check_numa_discovery)

static int s_test_sanity_check_environment_loader(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;

    aws_common_library_init(allocator);
    struct aws_system_environment *env = aws_system_environment_load(allocator);
    ASSERT_NOT_NULL(env);
    struct aws_byte_cursor virt_vendor = aws_system_environment_get_virtualization_vendor(env);
    ASSERT_TRUE(aws_byte_cursor_is_valid(&virt_vendor));
    struct aws_byte_cursor virt_product = aws_system_environment_get_virtualization_product_name(env);
    ASSERT_TRUE(aws_byte_cursor_is_valid(&virt_product));

    aws_system_environment_release(env);

    aws_common_library_clean_up();
    return 0;
}

AWS_TEST_CASE(test_sanity_check_environment_loader, s_test_sanity_check_environment_loader)
