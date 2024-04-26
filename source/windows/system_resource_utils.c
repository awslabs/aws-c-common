/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/common/system_resource_util.h>

#include <windows.h>

#include <psapi.h>

int aws_init_memory_usage_for_current_process(struct aws_memory_usage_stats *memory_usage) {
    AWS_PRECONDITION(memory_usage);

    AWS_ZERO_STRUCT(*memory_usage);
    HANDLE hProcess = GetCurrentProcess();

    PROCESS_MEMORY_COUNTERS pmc;

    BOOL ret = GetProcessMemoryInfo(hProcess, &pmc, sizeof(pmc));
    CloseHandle(hProcess);

    if (!ret) {
        return aws_raise_error(AWS_ERROR_SYS_CALL_FAILURE);
    }

    memory_usage->maxrss = pmc.PeakWorkingSetSize;
    memory_usage->page_faults = pmc.PageFaultCount;

    return AWS_OP_SUCCESS;
}
