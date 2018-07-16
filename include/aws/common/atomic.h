#ifndef AWS_COMMON_ATOMIC_H
#define AWS_COMMON_ATOMIC_H

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

#include <aws/common/common.h>

#ifdef __cplusplus
extern "C" {
#endif

/**
 * Sets `dst` to `value` if `compare` equals `dst`.
 * Returns 1 of the value was set, 0 otherwise.
 */
AWS_COMMON_API int aws_atomic_cas(int *dst, int compare, int value);

/**
 * Sets `dst` to `value` if `compare` equals `dst`.
 * Returns 1 of the value was set, 0 otherwise.
 */
AWS_COMMON_API int aws_atomic_cas_ptr(void **dst, void *compare, void *value);

#ifdef __cplusplus
}
#endif

#endif /* AWS_COMMON_ATOMIC_H */
