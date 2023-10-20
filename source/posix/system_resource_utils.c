/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/common/system_resource_util.h>

#include <sys/resource.h>

int aws_resource_usage_for_current_process(struct aws_resource_usage *ru) {
    AWS_PRECONDITION(ru);

    struct rusage usage;

    if (getrusage(RUSAGE_SELF, &usage)) {
        return aws_raise_error(AWS_ERROR_SYS_CALL_FAILURE);
    }

#if defined(AWS_OS_APPLE)
    ru->maxrss = usage.ru_maxrss / 1024;
#else
    ru->maxrss = usage.ru_maxrss;
#endif
    ru->page_faults = usage.ru_majflt;
    return AWS_OP_SUCCESS;
}
