#ifndef AWS_COMMON_CLOCK_INL
#define AWS_COMMON_CLOCK_INL

/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/common/clock.h>
#include <aws/common/common.h>
#include <aws/common/math.h>

AWS_EXTERN_C_BEGIN

/**
 * Converts 'timestamp' from unit 'convert_from' to unit 'convert_to', if the units are the same then 'timestamp' is
 * returned. If 'remainder' is NOT NULL, it will be set to the remainder if convert_from is a more precise unit than
 * convert_to. To avoid unnecessary branching, 'remainder' is not zero initialized in this function, be sure to set it
 * to 0 first if you care about that kind of thing. If conversion would lead to integer overflow, the timestamp
 * returned will be the highest possible time that is representable, i.e. UINT64_MAX.
 */
AWS_STATIC_IMPL uint64_t aws_timestamp_convert_u64(
    uint64_t timestamp,
    uint64_t convert_from_frequency,
    uint64_t convert_to_frequency,
    uint64_t *remainder) {
    uint64_t diff = 0;

    if (convert_to_frequency > convert_from_frequency) {
        diff = convert_to_frequency / convert_from_frequency;
        return aws_mul_u64_saturating(timestamp, diff);
    } else if (convert_to_frequency < convert_from_frequency) {
        diff = convert_from_frequency / convert_to_frequency;

        if (remainder) {
            *remainder = timestamp % diff;
        }

        return timestamp / diff;
    } else {
        return timestamp;
    }
}

AWS_STATIC_IMPL uint64_t aws_timestamp_convert(
    uint64_t timestamp,
    enum aws_timestamp_unit convert_from,
    enum aws_timestamp_unit convert_to,
    uint64_t *remainder) {

    return aws_timestamp_convert_u64(timestamp, convert_from, convert_to, remainder);
}

AWS_STATIC_IMPL uint64_t aws_timestamp_convert_ticks(
    uint64_t ticks,
    uint64_t old_frequency, 
    uint64_t new_frequency) {

    AWS_FATAL_ASSERT(old_frequency > 0 && new_frequency > 0);

    uint64_t old_seconds_elapsed = ticks / old_frequency;
    uint64_t old_remainder = ticks - old_seconds_elapsed * old_frequency;
    
    uint64_t new_ticks_whole = aws_mul_u64_saturating(old_seconds_elapsed, new_frequency);
    uint64_t new_ticks_remainder = aws_mul_u64_saturating(old_remainder, new_frequency) / old_frequency;

    return aws_add_u64_saturating(new_ticks_whole, new_ticks_remainder);
}

AWS_EXTERN_C_END

#endif /* AWS_COMMON_CLOCK_INL */
