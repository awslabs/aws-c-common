/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/common/system_resource_util.h>
#include <aws/common/logging.h>

#include <sys/resource.h>

#if defined(AWS_OS_APPLE)
#include <mach/mach.h>
#else
#include <aws/common/file.h>
#include <unistd.h>
#endif

/*
 * TODO:
 * use mallinfo2 to get malloc view into how much is allocated? seems missing on
 * anything non-glibc
*/

int aws_init_memory_usage_for_current_process(struct aws_memory_usage_stats *memory_usage) {
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
        return aws_raise_error(AWS_ERROR_SYS_CALL_FAILURE);
    }

    memory_usage->maxrss = usage.ru_maxrss;
    memory_usage->rss = rss;
#endif
    memory_usage->page_faults = usage.ru_majflt;
    return AWS_OP_SUCCESS;
}
