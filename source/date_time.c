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
#include <aws/common/date_time.h>

#include <aws/common/array_list.h>
#include <aws/common/byte_buf.h>
#include <aws/common/byte_order.h>
#include <aws/common/clock.h>
#include <aws/common/string.h>
#include <aws/common/time.h>

#include <ctype.h>
#include <math.h>

static const char *RFC822_DATE_FORMAT_STR_MINUS_Z = "%a, %d %b %Y %H:%M:%S GMT";
static const char *RFC822_DATE_FORMAT_STR_WITH_Z = "%a, %d %b %Y %H:%M:%S %Z";
static const char *ISO_8601_LONG_DATE_FORMAT_STR = "%Y-%m-%dT%H:%M:%SZ";

#define STR_TRIPLET_TO_INDEX(str)                                                                                      \
    (((uint32_t)(uint8_t)tolower((str)[0]) << 0) | ((uint32_t)(uint8_t)tolower((str)[1]) << 8) |                       \
     ((uint32_t)(uint8_t)tolower((str)[2]) << 16))

static uint32_t s_jan = 0;
static uint32_t s_feb = 0;
static uint32_t s_mar = 0;
static uint32_t s_apr = 0;
static uint32_t s_may = 0;
static uint32_t s_jun = 0;
static uint32_t s_jul = 0;
static uint32_t s_aug = 0;
static uint32_t s_sep = 0;
static uint32_t s_oct = 0;
static uint32_t s_nov = 0;
static uint32_t s_dec = 0;

static uint32_t s_utc = 0;
static uint32_t s_gmt = 0;

static void s_check_init_str_to_int(void) {
    if (!s_jan) {
        s_jan = STR_TRIPLET_TO_INDEX("jan");
        s_feb = STR_TRIPLET_TO_INDEX("feb");
        s_mar = STR_TRIPLET_TO_INDEX("mar");
        s_apr = STR_TRIPLET_TO_INDEX("apr");
        s_may = STR_TRIPLET_TO_INDEX("may");
        s_jun = STR_TRIPLET_TO_INDEX("jun");
        s_jul = STR_TRIPLET_TO_INDEX("jul");
        s_aug = STR_TRIPLET_TO_INDEX("aug");
        s_sep = STR_TRIPLET_TO_INDEX("sep");
        s_oct = STR_TRIPLET_TO_INDEX("oct");
        s_nov = STR_TRIPLET_TO_INDEX("nov");
        s_dec = STR_TRIPLET_TO_INDEX("dec");
        s_utc = STR_TRIPLET_TO_INDEX("utc");
        s_gmt = STR_TRIPLET_TO_INDEX("gmt");
    }
}

/* Get the 0-11 monthy number from a string representing Month. Case insensitive and will stop on abbreviation*/
static int get_month_number_from_str(const char *time_string, size_t start_index, size_t stop_index) {
    s_check_init_str_to_int();

    if (stop_index - start_index < 3) {
        return -1;
    }

    /* This AND forces the string to lowercase (assuming ASCII) */
    uint32_t comp_val = STR_TRIPLET_TO_INDEX(time_string + start_index);

    /* this can't be a switch, because I can't make it a constant expression. */
    if (s_jan == comp_val) {
        return 0;
    }

    if (s_feb == comp_val) {
        return 1;
    }

    if (s_mar == comp_val) {
        return 2;
    }

    if (s_apr == comp_val) {
        return 3;
    }

    if (s_may == comp_val) {
        return 4;
    }

    if (s_jun == comp_val) {
        return 5;
    }

    if (s_jul == comp_val) {
        return 6;
    }

    if (s_aug == comp_val) {
        return 7;
    }

    if (s_sep == comp_val) {
        return 8;
    }

    if (s_oct == comp_val) {
        return 9;
    }

    if (s_nov == comp_val) {
        return 10;
    }

    if (s_dec == comp_val) {
        return 11;
    }

    return -1;
}

/* Detects whether or not the passed in timezone string is a UTC zone. */
static bool is_utc_time_zone(const char *str) {
    s_check_init_str_to_int();

    size_t len = strlen(str);

    if (len > 0) {
        if (str[0] == 'Z') {
            return true;
        }

        if (len > 3 && (str[0] == '+' || str[0] == '-')) {
            if (!strcmp("+0000", str) || !strcmp("-0000", str)) {
                return true;
            }

            return false;
        }
    }

    if (len < 3) {
        return false;
    }

    uint32_t comp_val = STR_TRIPLET_TO_INDEX(str);

    if (comp_val == s_utc || comp_val == s_gmt) {
        return true;
    }

    return false;
}

struct tm s_get_time_struct(struct aws_date_time *dt, bool local_time) {
    struct tm time;
    AWS_ZERO_STRUCT(time);
    if (local_time) {
        aws_localtime(dt->timestamp, &time);
    } else {
        aws_gmtime(dt->timestamp, &time);
    }

    return time;
}

void aws_date_time_init_now(struct aws_date_time *dt) {
    uint64_t current_time = 0;
    aws_sys_clock_get_ticks(&current_time);
    dt->timestamp = (time_t)aws_timestamp_convert(current_time, AWS_TIMESTAMP_NANOS, AWS_TIMESTAMP_SECS, NULL);
    dt->gmt_time = s_get_time_struct(dt, false);
    dt->local_time = s_get_time_struct(dt, true);
}

void aws_date_time_init_epoch_millis(struct aws_date_time *dt, uint64_t ms_since_epoch) {
    dt->timestamp = (time_t)(ms_since_epoch / AWS_TIMESTAMP_MILLIS);
    dt->gmt_time = s_get_time_struct(dt, false);
    dt->local_time = s_get_time_struct(dt, true);
}

void aws_date_time_init_epoch_secs(struct aws_date_time *dt, double sec_ms) {
    dt->timestamp = (time_t)sec_ms;
    dt->gmt_time = s_get_time_struct(dt, false);
    dt->local_time = s_get_time_struct(dt, true);
}

static int s_parse_iso_8601(const struct aws_byte_buf *date_str, struct tm *parsed_time) {
    size_t index = 0;
    size_t state_start_index = 0;
    const int final_state = 7;
    int state = 0;
    bool error = false;

    while (!error && index < date_str->len) { /* lgtm [cpp/constant-comparison] */
        char c = date_str->buffer[index];
        switch (state) {
            case 0:
                if (c == '-' && index - state_start_index == 4) {
                    state = 1;
                    state_start_index = index + 1;
                    parsed_time->tm_year -= 1900;
                } else if (isdigit(c)) {
                    parsed_time->tm_year = parsed_time->tm_year * 10 + (c - '0');
                } else {
                    error = true;
                }
                break;
            case 1:
                if (c == '-' && index - state_start_index == 2) {
                    state = 2;
                    state_start_index = index + 1;
                    parsed_time->tm_mon -= 1;
                } else if (isdigit(c)) {
                    parsed_time->tm_mon = parsed_time->tm_mon * 10 + (c - '0');
                } else {
                    error = true;
                }

                break;
            case 2:
                if (c == 'T' && index - state_start_index == 2) {
                    state = 3;
                    state_start_index = index + 1;
                } else if (isdigit(c)) {
                    parsed_time->tm_mday = parsed_time->tm_mday * 10 + (c - '0');
                } else {
                    error = true;
                }

                break;
            case 3:
                if (c == ':' && index - state_start_index == 2) {
                    state = 4;
                    state_start_index = index + 1;
                } else if (isdigit(c)) {
                    parsed_time->tm_hour = parsed_time->tm_hour * 10 + (c - '0');
                } else {
                    error = true;
                }

                break;
            case 4:
                if (c == ':' && index - state_start_index == 2) {
                    state = 5;
                    state_start_index = index + 1;
                } else if (isdigit(c)) {
                    parsed_time->tm_min = parsed_time->tm_min * 10 + (c - '0');
                } else {
                    error = true;
                }

                break;
            case 5:
                if (c == 'Z' && index - state_start_index == 2) {
                    state = final_state;
                    state_start_index = index + 1;
                } else if (c == '.' && index - state_start_index == 2) {
                    state = 6;
                    state_start_index = index + 1;
                } else if (isdigit(c)) {
                    parsed_time->tm_sec = parsed_time->tm_sec * 10 + (c - '0');
                } else {
                    error = true;
                }

                break;
            case 6:
                if (c == 'Z') {
                    state = final_state;
                    state_start_index = index + 1;
                } else if (!isdigit(c)) {
                    error = true;
                }
                break;
        }
        index++;
    }

    return state == final_state && !error ? AWS_OP_SUCCESS : AWS_OP_ERR;
}

static int s_parse_rfc_822(const struct aws_byte_buf *date_str, struct tm *parsed_time, struct aws_date_time *dt) {
    size_t len = date_str->len;

    size_t index = 0;
    size_t state_start_index = 0;
    int final_state = 8;
    int state = 0;
    bool error = false;

    while (!error && index < len) {
        char c = date_str->buffer[index];

        switch (state) {
            case 0:
                if (c == ',') {
                    state = 1;
                    state_start_index = index + 1;
                } else if (!isalpha(c)) {
                    error = true;
                }
                break;
            case 1:
                if (isspace(c)) {
                    state = 2;
                    state_start_index = index + 1;
                } else {
                    error = true;
                }
                break;
            case 2:
                if (isdigit(c)) {
                    parsed_time->tm_mday = parsed_time->tm_mday * 10 + (c - '0');
                } else if (isspace(c)) {
                    state = 3;
                    state_start_index = index + 1;
                } else {
                    error = true;
                }
                break;
            case 3:
                if (isspace(c)) {
                    int monthNumber =
                        get_month_number_from_str((const char *)date_str->buffer, state_start_index, index + 1);

                    if (monthNumber > -1) {
                        state = 4;
                        state_start_index = index + 1;
                        parsed_time->tm_mon = monthNumber;
                    } else {
                        error = true;
                    }
                } else if (!isalpha(c)) {
                    error = true;
                }
                break;
            case 4:
                if (isspace(c) && index - state_start_index == 4) {
                    state = 5;
                    state_start_index = index + 1;
                    parsed_time->tm_year -= 1900;
                } else if (isspace(c) && index - state_start_index == 2) {
                    state = 5;
                    state_start_index = index + 1;
                    parsed_time->tm_year += 2000 - 1900;
                } else if (isdigit(c)) {
                    parsed_time->tm_year = parsed_time->tm_year * 10 + (c - '0');
                } else {
                    error = true;
                }
                break;
            case 5:
                if (c == ':' && index - state_start_index == 2) {
                    state = 6;
                    state_start_index = index + 1;
                } else if (isdigit(c)) {
                    parsed_time->tm_hour = parsed_time->tm_hour * 10 + (c - '0');
                } else {
                    error = true;
                }
                break;
            case 6:
                if (c == ':' && index - state_start_index == 2) {
                    state = 7;
                    state_start_index = index + 1;
                } else if (isdigit(c)) {
                    parsed_time->tm_min = parsed_time->tm_min * 10 + (c - '0');
                } else {
                    error = true;
                }
                break;
            case 7:
                if (isspace(c) && index - state_start_index == 2) {
                    state = 8;
                    state_start_index = index + 1;
                } else if (isdigit(c)) {
                    parsed_time->tm_sec = parsed_time->tm_sec * 10 + (c - '0');
                } else {
                    error = true;
                }
                break;
            case 8:
                if (isalpha(c) && (index - state_start_index) < 5) {
                    dt->tz[index - state_start_index] = c;
                }

                break;
        }

        index++;
    }

    if (dt->tz[0] != 0) {
        dt->utc_assumed = is_utc_time_zone(dt->tz);
    }

    return error || state != final_state ? AWS_OP_ERR : AWS_OP_SUCCESS;
}

int aws_date_time_init_from_str(
    struct aws_date_time *dt,
    const struct aws_byte_buf *date_str,
    enum aws_date_format fmt) {
    if (date_str->len > AWS_DATE_TIME_STR_MAX_LEN) {
        return aws_raise_error(AWS_ERROR_OVERFLOW_DETECTED);
    }

    AWS_ZERO_STRUCT(*dt);

    struct tm parsed_time;
    AWS_ZERO_STRUCT(parsed_time);
    bool successfully_parsed = false;
    if (fmt == AWS_DATE_FORMAT_ISO_8601 || fmt == AWS_DATE_FORMAT_AUTO_DETECT) {
        if (!s_parse_iso_8601(date_str, &parsed_time)) {
            dt->utc_assumed = true;
            successfully_parsed = true;
        }
    }

    if (fmt == AWS_DATE_FORMAT_RFC822 || (fmt == AWS_DATE_FORMAT_AUTO_DETECT && !successfully_parsed)) {
        if (!s_parse_rfc_822(date_str, &parsed_time, dt)) {
            successfully_parsed = true;
        }
    }

    if (!successfully_parsed) {
        return aws_raise_error(AWS_ERROR_INVALID_DATE_STR);
    }

    if (dt->utc_assumed) {
        dt->timestamp = aws_timegm(&parsed_time);
    } else {
        dt->timestamp = mktime(&parsed_time);
    }

    dt->gmt_time = s_get_time_struct(dt, false);
    dt->local_time = s_get_time_struct(dt, true);

    return AWS_OP_SUCCESS;
}

int aws_date_time_to_local_time_str(
    struct aws_date_time *dt,
    enum aws_date_format fmt,
    struct aws_byte_buf *output_buf) {
    assert(fmt != AWS_DATE_FORMAT_AUTO_DETECT);

    if (AWS_UNLIKELY(fmt == AWS_DATE_FORMAT_AUTO_DETECT)) {
        return aws_raise_error(AWS_ERROR_INVALID_ARGUMENT);
    }

    char formatted_string[AWS_DATE_TIME_STR_MAX_LEN];
    AWS_ZERO_ARRAY(formatted_string);

    if (fmt == AWS_DATE_FORMAT_RFC822) {
        strftime(formatted_string, sizeof(formatted_string), RFC822_DATE_FORMAT_STR_WITH_Z, &dt->local_time);
    } else {
        strftime(formatted_string, sizeof(formatted_string), ISO_8601_LONG_DATE_FORMAT_STR, &dt->local_time);
    }

    size_t len = strlen(formatted_string);

    if (output_buf->capacity < len) {
        return aws_raise_error(AWS_ERROR_SHORT_BUFFER);
    }

    memcpy(output_buf->buffer, formatted_string, len);
    output_buf->len = len;

    return AWS_OP_SUCCESS;
}

int aws_date_time_to_utc_time_str(struct aws_date_time *dt, enum aws_date_format fmt, struct aws_byte_buf *output_buf) {
    assert(fmt != AWS_DATE_FORMAT_AUTO_DETECT);

    if (AWS_UNLIKELY(fmt == AWS_DATE_FORMAT_AUTO_DETECT)) {
        return aws_raise_error(AWS_ERROR_INVALID_ARGUMENT);
    }

    char formatted_string[AWS_DATE_TIME_STR_MAX_LEN];
    AWS_ZERO_ARRAY(formatted_string);

    if (fmt == AWS_DATE_FORMAT_RFC822) {
        strftime(formatted_string, sizeof(formatted_string), RFC822_DATE_FORMAT_STR_MINUS_Z, &dt->gmt_time);
    } else {
        strftime(formatted_string, sizeof(formatted_string), ISO_8601_LONG_DATE_FORMAT_STR, &dt->gmt_time);
    }

    size_t len = strlen(formatted_string);

    if (output_buf->capacity < len) {
        return aws_raise_error(AWS_ERROR_SHORT_BUFFER);
    }

    memcpy(output_buf->buffer, formatted_string, len);
    output_buf->len = len;

    return AWS_OP_SUCCESS;
}

double aws_date_time_as_epoch_secs(struct aws_date_time *dt) {
    return (double)dt->timestamp;
}

uint64_t aws_date_time_as_nanos(struct aws_date_time *dt) {
    return (uint64_t)dt->timestamp * AWS_TIMESTAMP_NANOS;
}

uint64_t aws_date_time_as_millis(struct aws_date_time *dt) {
    return (uint64_t)dt->timestamp * AWS_TIMESTAMP_MILLIS;
}

uint16_t aws_date_time_year(struct aws_date_time *dt, bool local_time) {
    struct tm *time = local_time ? &dt->local_time : &dt->gmt_time;

    return (uint16_t)(time->tm_year + 1900);
}

enum aws_date_month aws_date_time_month(struct aws_date_time *dt, bool local_time) {
    struct tm *time = local_time ? &dt->local_time : &dt->gmt_time;

    return time->tm_mon;
}

uint8_t aws_date_time_month_day(struct aws_date_time *dt, bool local_time) {
    struct tm *time = local_time ? &dt->local_time : &dt->gmt_time;

    return (uint8_t)time->tm_mday;
}

enum aws_date_day_of_week aws_date_time_day_of_week(struct aws_date_time *dt, bool local_time) {
    struct tm *time = local_time ? &dt->local_time : &dt->gmt_time;

    return time->tm_wday;
}

uint8_t aws_date_time_hour(struct aws_date_time *dt, bool local_time) {
    struct tm *time = local_time ? &dt->local_time : &dt->gmt_time;

    return (uint8_t)time->tm_hour;
}

uint8_t aws_date_time_minute(struct aws_date_time *dt, bool local_time) {
    struct tm *time = local_time ? &dt->local_time : &dt->gmt_time;

    return (uint8_t)time->tm_min;
}

uint8_t aws_date_time_second(struct aws_date_time *dt, bool local_time) {
    struct tm *time = local_time ? &dt->local_time : &dt->gmt_time;

    return (uint8_t)time->tm_sec;
}

bool aws_date_time_dst(struct aws_date_time *dt, bool local_time) {
    struct tm *time = local_time ? &dt->local_time : &dt->gmt_time;

    return (bool)time->tm_isdst;
}

int64_t aws_date_time_diff(struct aws_date_time *a, struct aws_date_time *b) {
    return (int64_t)a->timestamp - (int64_t)b->timestamp;
}
