#ifndef AWS_COMMON_CLOCK_H
#define AWS_COMMON_CLOCK_H

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

enum aws_timestamp_unit {
    AWS_TIMESTAMP_SECS = 1,
    AWS_TIMESTAMP_MILLIS = 1000,
    AWS_TIMESTAMP_MICROS = 1000000,
    AWS_TIMESTAMP_NANOS = 1000000000
};

/**
 * Converts 'timestamp' from unit 'convert_from' to unit 'convert_to', if the units are the same then 'timestamp' is returned.
 */
static inline uint64_t aws_timestamp_convert(uint64_t timestamp, enum aws_timestamp_unit convert_from, enum aws_timestamp_unit convert_to) {
    uint64_t diff = 0;

    if (convert_to >  convert_from) {
        diff = convert_to / convert_from;
        return timestamp * diff;
    }
    else if (convert_to < convert_from) {
        diff = convert_from / convert_to;
        return timestamp / diff;
    }
    else {
        return timestamp;
    }
}

#ifdef __cplusplus
extern "C" {
#endif
/**
 * Get ticks in nanoseconds (usually 100 nanosecond precision) on the high resolution clock (most-likely TSC). This
 * clock has no bearing on the actual system time. On success, timestamp will be set.
 */
AWS_COMMON_API
int aws_high_res_clock_get_ticks(uint64_t *timestamp);

/**
 * Get ticks in nanoseconds (usually 100 nanosecond precision) on the system clock. Reflects actual system time via
 * nanoseconds since unix epoch. Use with care since an inaccurately set clock will probably cause bugs. On success,
 * timestamp will be set.
 */
AWS_COMMON_API
int aws_sys_clock_get_ticks(uint64_t *timestamp);

#ifdef __cplusplus
}
#endif

#endif /* AWS_COMMON_CLOCK_H */
