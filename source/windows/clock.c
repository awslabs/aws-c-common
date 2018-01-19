/*
* Copyright 2010-2018 Amazon.com, Inc. or its affiliates. All Rights Reserved.
*
* Licensed under the Apache License, Version 2.0 (the "License").
* You may not use this file except in compliance with the License.
* A copy of the License is located at
*
*  http://aws.amazon.com/apache2.0
*
* or in the "license" file accompanying this file. This file is distributed
* on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
* express or implied. See the License for the specific language governing
* permissions and limitations under the License.
*/

#include <aws/common/clock.h>
#include <Windows.h>

static const uint64_t MUS_PER_SEC = 1000000;
static const uint64_t NS_PER_MUS = 1000;
static const uint64_t FILE_TIME_TO_NS = 100;
static const uint64_t EC_TO_UNIX_EPOCH = 11644473600LL;
static const uint64_t WINDOWS_TICK = 10000000;

int aws_high_res_clock_get_ticks(uint64_t *timestamp) {
    LARGE_INTEGER ticks, frequency;
    /* QPC runs on sub-microsecond precision, convert to nanoseconds */
    if (QueryPerformanceFrequency(&frequency) && QueryPerformanceCounter(&ticks)) {
        *timestamp = (((uint64_t)ticks.QuadPart * MUS_PER_SEC) / (uint64_t)frequency.QuadPart) * NS_PER_MUS;
        return AWS_OP_SUCCESS;
    }

    return aws_raise_error(AWS_ERROR_CLOCK_FAILURE);
}

int aws_sys_clock_get_ticks(uint64_t *timestamp) {
    FILETIME ticks;
    /*GetSystemTimePreciseAsFileTime() returns 100 nanosecond precision. Convert to nanoseconds.
     *Also, this function returns a different epoch than unix, so we add a conversion to handle that as well. */
    GetSystemTimePreciseAsFileTime(&ticks);

    /*if this looks unnecessary, see: https://msdn.microsoft.com/en-us/library/windows/desktop/ms724284(v=vs.85).aspx */
    ULARGE_INTEGER int_conv;
    int_conv.LowPart = ticks.dwLowDateTime;
    int_conv.HighPart = ticks.dwHighDateTime;

    *timestamp = (int_conv.QuadPart - (WINDOWS_TICK * EC_TO_UNIX_EPOCH)) * FILE_TIME_TO_NS;
    return AWS_OP_SUCCESS;
}
