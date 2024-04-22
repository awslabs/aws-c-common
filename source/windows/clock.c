/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/common/clock.h>
#include <windows.h>

static const uint64_t FILE_TIME_TO_NS = 100;
static const uint64_t EC_TO_UNIX_EPOCH = 11644473600LL;
static const uint64_t WINDOWS_TICK = 10000000;

static INIT_ONCE s_timefunc_init_once = INIT_ONCE_STATIC_INIT;
typedef VOID WINAPI timefunc_t(LPFILETIME);
static VOID WINAPI s_get_system_time_func_lazy_init(LPFILETIME filetime_p);
static timefunc_t *volatile s_p_time_func = s_get_system_time_func_lazy_init;

/* Convert a string from a macro to a wide string */
#define WIDEN2(s) L## #s
#define WIDEN(s) WIDEN2(s)

static BOOL CALLBACK s_get_system_time_init_once(PINIT_ONCE init_once, PVOID param, PVOID *context) {
    (void)init_once;
    (void)param;
    (void)context;

    HMODULE kernel = GetModuleHandleW(WIDEN(WINDOWS_KERNEL_LIB) L".dll");
    timefunc_t *time_func = (timefunc_t *)GetProcAddress(kernel, "GetSystemTimePreciseAsFileTime");

    if (time_func == NULL) {
        time_func = GetSystemTimeAsFileTime;
    }

    s_p_time_func = time_func;

    return TRUE;
}

static VOID WINAPI s_get_system_time_func_lazy_init(LPFILETIME filetime_p) {
    BOOL status = InitOnceExecuteOnce(&s_timefunc_init_once, s_get_system_time_init_once, NULL, NULL);

    if (status) {
        (*s_p_time_func)(filetime_p);
    } else {
        /* Something went wrong in static initialization? Should never happen, but deal with it somehow...*/
        GetSystemTimeAsFileTime(filetime_p);
    }
}

int aws_high_res_clock_get_ticks(uint64_t *timestamp) {
    LARGE_INTEGER ticks, frequency;
    /* QPC runs on sub-microsecond precision, convert to nanoseconds */
    if (QueryPerformanceFrequency(&frequency) && QueryPerformanceCounter(&ticks)) {
        *timestamp = aws_timestamp_convert_u64(
            (uint64_t)ticks.QuadPart, (uint64_t)frequency.QuadPart, AWS_TIMESTAMP_NANOS, NULL);

        return AWS_OP_SUCCESS;
    }

    return aws_raise_error(AWS_ERROR_CLOCK_FAILURE);
}

int aws_sys_clock_get_ticks(uint64_t *timestamp) {
    FILETIME ticks;
    /*GetSystemTimePreciseAsFileTime() returns 100 nanosecond precision. Convert to nanoseconds.
     *Also, this function returns a different epoch than unix, so we add a conversion to handle that as well. */
    (*s_p_time_func)(&ticks);

    /*if this looks unnecessary, see:
     * https://msdn.microsoft.com/en-us/library/windows/desktop/ms724284(v=vs.85).aspx
     */
    ULARGE_INTEGER int_conv;
    int_conv.LowPart = ticks.dwLowDateTime;
    int_conv.HighPart = ticks.dwHighDateTime;

    *timestamp = (int_conv.QuadPart - (WINDOWS_TICK * EC_TO_UNIX_EPOCH)) * FILE_TIME_TO_NS;
    return AWS_OP_SUCCESS;
}
