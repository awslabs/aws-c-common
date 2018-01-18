#ifndef AWS_COMMON_CLOCK_H_
#define AWS_COMMON_CLOCK_H_

/*
* Copyright 2010-2017 Amazon.com, Inc. or its affiliates. All Rights Reserved.
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
#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif
/**
 * Get ticks in nanoseconds (usually 100 nanosecond precision) on the high resolution clock (most-likely TSC). This clock has no bearing on the actual
 * system time. On success, timestamp will be set.
 */
AWS_COMMON_API int aws_high_res_clock_get_ticks(uint64_t *timestamp);

/**
 * Get ticks in nanoseconds (usually 100 nanosecond precision) on the system clock. Reflects actual system time via nanoseconds since unix epoch.
 * Use with care since an inaccurately set clock will probably cause bugs. On success, timestamp will be set.
 */
AWS_COMMON_API int aws_sys_clock_get_ticks(uint64_t *timestamp);

#ifdef __cplusplus
}
#endif

#endif /* AWS_COMMON_CLOCK_H_*/