#ifndef AWS_COMMON_DATE_TIME_H
#define AWS_COMMON_DATE_TIME_H
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

#include <time.h>

struct aws_byte_buf;

enum aws_date_format {
    AWS_DATE_FORMAT_RFC822,
    AWS_DATE_FORMAT_ISO_8601,
    AWS_DATE_FORMAT_AUTO_DETECT,
};

enum aws_date_month {
    AWS_DATE_MONTH_JANUARY = 0,
    AWS_DATE_MONTH_FEBRUARY,
    AWS_DATE_MONTH_MARCH,
    AWS_DATE_MONTH_APRIL,
    AWS_DATE_MONTH_MAY,
    AWS_DATE_MONTH_JUNE,
    AWS_DATE_MONTH_JULY,
    AWS_DATE_MONTH_AUGUST,
    AWS_DATE_MONTH_SEPTEMBER,
    AWS_DATE_MONTH_OCTOBER,
    AWS_DATE_MONTH_NOVEMBER,
    AWS_DATE_MONTH_DECEMBER,
};

enum aws_date_day_of_week {
    AWS_DATE_DAY_OF_WEEK_SUNDAY = 0,
    AWS_DATE_DAY_OF_WEEK_MONDAY,
    AWS_DATE_DAY_OF_WEEK_TUESDAY,
    AWS_DATE_DAY_OF_WEEK_WEDNESDAY,
    AWS_DATE_DAY_OF_WEEK_THURSDAY,
    AWS_DATE_DAY_OF_WEEK_FRIDAY,
    AWS_DATE_DAY_OF_WEEK_SATURDAY,
};

struct aws_date_time {
    time_t timestamp;
    char tz[5];
    bool utc_assumed;
};

AWS_EXTERN_C_BEGIN

/**
 * Initializes dt to be the current system time.
 */
AWS_COMMON_API void aws_date_time_init_now(struct aws_date_time *dt);

/**
 * Initializes dt to be the time represented in milliseconds since unix epoch.
 */
AWS_COMMON_API void aws_date_time_init_epoch_millis(struct aws_date_time *dt, uint64_t ns_since_epoch);

/**
 * Initializes dt to be the time represented in seconds.millis since unix epoch.
 */
AWS_COMMON_API void aws_date_time_init_epoch_secs(struct aws_date_time *dt, double sec_ms);

/**
 * Initializes dt to be the time represented by date_str in format 'fmt'. Returns AWS_OP_SUCCESS if the
 * string was succesfully parsed, returns  AWS_OP_ERR if parsing failed.
 */
AWS_COMMON_API int aws_date_time_init_from_str(
    struct aws_date_time *dt,
    const struct aws_byte_buf *date_str,
    enum aws_date_format fmt);

/**
 * Copies the current time as a formatted date string in local time into output_buf. If buffer is too small, it will
 * return AWS_OP_ERR. A good size suggestion is 100 bytes. AWS_DATE_FORMAT_AUTO_DETECT is not allowed.
 */
AWS_COMMON_API int aws_date_time_to_local_time_str(
    struct aws_date_time *dt,
    enum aws_date_format fmt,
    struct aws_byte_buf *output_buf);

/**
 * Copies the current time as a formatted date string in utc time into output_buf. If buffer is too small, it will
 * return AWS_OP_ERR. A good size suggestion is 100 bytes. AWS_DATE_FORMAT_AUTO_DETECT is not allowed.
 */
AWS_COMMON_API int aws_date_time_to_utc_time_str(
    struct aws_date_time *dt,
    enum aws_date_format fmt,
    struct aws_byte_buf *output_buf);
AWS_COMMON_API double aws_date_time_as_epoch_secs(struct aws_date_time *dt);
AWS_COMMON_API uint64_t aws_date_time_as_nanos(struct aws_date_time *dt);
AWS_COMMON_API uint64_t aws_date_time_as_millis(struct aws_date_time *dt);
AWS_COMMON_API uint16_t aws_date_time_year(struct aws_date_time *dt, bool local_time);
AWS_COMMON_API enum aws_date_month aws_date_time_month(struct aws_date_time *dt, bool local_time);
AWS_COMMON_API uint8_t aws_date_time_month_day(struct aws_date_time *dt, bool local_time);
AWS_COMMON_API enum aws_date_day_of_week aws_date_time_day_of_week(struct aws_date_time *dt, bool local_time);
AWS_COMMON_API uint8_t aws_date_time_hour(struct aws_date_time *dt, bool local_time);
AWS_COMMON_API uint8_t aws_date_time_minute(struct aws_date_time *dt, bool local_time);
AWS_COMMON_API uint8_t aws_date_time_second(struct aws_date_time *dt, bool local_time);
AWS_COMMON_API bool aws_date_time_dst(struct aws_date_time *dt, bool local_time);
AWS_COMMON_API int64_t aws_date_time_diff(struct aws_date_time *a, struct aws_date_time *b);

AWS_EXTERN_C_END

#endif /* AWS_COMMON_DATE_TIME_H */