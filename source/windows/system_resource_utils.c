/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/common/system_resource_util.h>

#include <psapi.h>
#include <windows.h>

int aws_resource_usage_for_current_process(struct aws_resource_usage *ru) {
    AWS_PRECONDITION(resource_usage);

    HANDLE hProcess = GetCurrentProcess();
    ;
    PROCESS_MEMORY_COUNTERS pmc;

    BOOL ret = GetProcessMemoryInfo(hProcess, &pmc, sizeof(pmc));
    CloseHandle(hProcess);

    if (!ret) {
        return aws_raise_error(AWS_ERROR_SYS_CALL_FAILURE);
    }

    ru->maxrss = pmc.PeakWorkingSetSize;
    ru->page_faults = pmc.PageFaultCount;

    return AWS_OP_SUCCESS;
}
