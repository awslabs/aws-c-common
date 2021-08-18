/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */
#include <aws/common/process.h>
#include <process.h>

/**
 * this is just the value it's hard coded to in windows NT and later
 * see https://docs.microsoft.com/en-us/windows/win32/sysinfo/kernel-objects
 * for more information.
 */
static const size_t s_max_handles = 1 << 24;

int aws_get_pid(void) {
#if defined(AWS_OS_WINDOWS_DESKTOP)
    return _getpid();
#else
    return -1;
#endif
}

size_t aws_get_soft_limit_io_handles(void) {
    return s_max_handles;
}

size_t aws_get_hard_limit_io_handles(void) {
    return s_max_handles;
}

int aws_set_soft_limit_io_handles(size_t max_handles) {
    (void)max_handles;

    return aws_raise_error(AWS_ERROR_UNIMPLEMENTED);
}
