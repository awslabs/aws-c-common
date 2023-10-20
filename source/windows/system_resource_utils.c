/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/common/system_resource_util.h>

#include <windows.h>

#include <psapi.h>


int aws_memory_usage_for_current_process(struct aws_memory_usage *mu) {
    AWS_PRECONDITION(mu);

    HANDLE hProcess = GetCurrentProcess();
    
    PROCESS_MEMORY_COUNTERS pmc;

    BOOL ret = GetProcessMemoryInfo(hProcess, &pmc, sizeof(pmc));
    CloseHandle(hProcess);

    if (!ret) {
        return aws_raise_error(AWS_ERROR_SYS_CALL_FAILURE);
    }

    mu->maxrss = pmc.PeakWorkingSetSize;
    mu->page_faults = pmc.PageFaultCount;

    return AWS_OP_SUCCESS;
}
