#ifndef AWS_COMMON_SYSTEM_RESOURCE_UTIL_H
#define AWS_COMMON_SYSTEM_RESOURCE_UTIL_H

/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */
#include <aws/common/common.h>

AWS_PUSH_SANE_WARNING_LEVEL

AWS_EXTERN_C_BEGIN

struct aws_resource_usage {
    size_t maxrss;
    size_t page_faults;

    size_t _reserved[8];
};

AWS_COMMON_API int aws_resource_usage_for_current_process(struct aws_resource_usage *resource_usage);

AWS_EXTERN_C_END
AWS_POP_SANE_WARNING_LEVEL

#endif /* AWS_COMMON_SYSTEM_RESOURCE_UTIL_H */
