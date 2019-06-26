#ifndef AWS_COMMON_COMMON_H
#define AWS_COMMON_COMMON_H

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

#include <aws/common/config.h>
#include <aws/common/exports.h>

#include <aws/common/allocator.h>
#include <aws/common/assert.h>
#include <aws/common/error.h>
#include <aws/common/macros.h>
#include <aws/common/stdbool.h>
#include <aws/common/stdint.h>
#include <stddef.h>
#include <stdio.h>
#include <stdlib.h> /* for abort() */
#include <string.h>

AWS_EXTERN_C_BEGIN

/**
 * Securely zeroes a memory buffer. This function will attempt to ensure that
 * the compiler will not optimize away this zeroing operation.
 */
AWS_COMMON_API
void aws_secure_zero(void *pBuf, size_t bufsize);

AWS_EXTERN_C_END

#include <aws/common/error_codes.h>

#endif /* AWS_COMMON_COMMON_H */
