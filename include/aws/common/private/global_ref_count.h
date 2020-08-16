#ifndef AWS_COMMON_GLOBAL_REFCOUNT_H
#define AWS_COMMON_GLOBAL_REFCOUNT_H

/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */
#include <aws/common/common.h>

AWS_EXTERN_C_BEGIN

AWS_COMMON_API void aws_global_thread_tracker_init(void);

AWS_COMMON_API void aws_global_thread_tracker_clean_up(void);

AWS_EXTERN_C_END

#endif /* AWS_COMMON_GLOBAL_REFCOUNT_H */
