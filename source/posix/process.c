/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/common/process.h>

#include <sys/resource.h>
#include <sys/time.h>
#include <unistd.h>

#if defined(AWS_OS_APPLE)
#include <mach/mach.h>
#else
#include <aws/common/file.h>
#include <unistd.h>
#endif

int aws_get_pid(void) {
    return (int)getpid();
}

size_t aws_get_soft_limit_io_handles(void) {
    struct rlimit rlimit;
    AWS_ZERO_STRUCT(rlimit);

    AWS_FATAL_ASSERT(
        !getrlimit(RLIMIT_NOFILE, &rlimit) &&
        "getrlimit() should never fail for RLIMIT_NOFILE regardless of user permissions");
    return rlimit.rlim_cur;
}

size_t aws_get_hard_limit_io_handles(void) {
    struct rlimit rlimit;
    AWS_ZERO_STRUCT(rlimit);

    AWS_FATAL_ASSERT(
        !getrlimit(RLIMIT_NOFILE, &rlimit) &&
        "getrlimit() should never fail for RLIMIT_NOFILE regardless of user permissions");
    return rlimit.rlim_max;
}

int aws_set_soft_limit_io_handles(size_t max_handles) {
    size_t hard_limit = aws_get_hard_limit_io_handles();

    if (max_handles > hard_limit) {
        return aws_raise_error(AWS_ERROR_INVALID_ARGUMENT);
    }

    struct rlimit rlimit = {
        .rlim_cur = max_handles,
        .rlim_max = hard_limit,
    };

    if (setrlimit(RLIMIT_NOFILE, &rlimit)) {
        return aws_raise_error(AWS_ERROR_INVALID_ARGUMENT);
    }

    return AWS_OP_SUCCESS;
}

/*
 * TODO:
 * use mallinfo2 to get malloc view into how much is allocated? seems missing on
 * anything non-glibc
*/

int aws_memory_usage_init_for_current_process(struct aws_memory_usage_info *memory_usage) {
    AWS_PRECONDITION(memory_usage);

    AWS_ZERO_STRUCT(*memory_usage);
    struct rusage usage;

    if (getrusage(RUSAGE_SELF, &usage)) {
        return aws_raise_error(AWS_ERROR_SYS_CALL_FAILURE);
    }

#if defined(AWS_OS_APPLE)
    struct mach_task_basic_info info;
    mach_msg_type_number_t infoCount = MACH_TASK_BASIC_INFO_COUNT;
    if (task_info(mach_task_self(), MACH_TASK_BASIC_INFO, (task_info_t)&info, &infoCount) != KERN_SUCCESS) {
        return aws_raise_error(AWS_ERROR_SYS_CALL_FAILURE);
    }

    memory_usage->maxrss = (size_t)info.resident_size_max;
    memory_usage->rss = (size_t)info.resident_size; 
#else
    FILE* statm = aws_fopen_safe("/proc/self/statm", "r");
    if (statm == NULL) {
        return aws_raise_error(AWS_ERROR_SYS_CALL_FAILURE);
    }

    long rss = 0; /* Note: procfs specifies it as long*/
    if (fscanf(statm, "%*s %ld", &rss) != 1) {
        fclose(statm);
        return aws_raise_error(AWS_ERROR_SYS_CALL_FAILURE);
    }

    fclose(statm);
    memory_usage->maxrss = usage.ru_maxrss;
    memory_usage->rss = (rss * (size_t)sysconf(_SC_PAGESIZE)) / 1024;
#endif
    return AWS_OP_SUCCESS;
}

