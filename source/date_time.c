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

#include <aws/common/byte_buf.h>
#include <aws/common/clock.h>
#include <aws/common/time.h>

#include <ctype.h>
#include <math.h>

static const char *RFC822_DATE_FORMAT_STR_MINUS_Z = "%a, %d %b %Y %H:%M:%S GMT";
static const char *RFC822_DATE_FORMAT_STR_WITH_Z = "%a, %d %b %Y %H:%M:%S %Z";
static const char *ISO_8601_LONG_DATE_FORMAT_STR = "%Y-%m-%dT%H:%M:%SZ";

static int get_week_day_number_from_str(const char *time_string, size_t startIndex, size_t stopIndex) {
    if (stopIndex - startIndex < 3) {
        return -1;
    }

    size_t index = startIndex;

    char c = time_string[index];
    char next = 0;

    /* it's ugly but this should compile down to EXACTLY 3 comparisons and no memory allocations */
    switch (c) {
        case 'S':
        case 's':
            next = time_string[++index];
            switch (next) {
                case 'A':
                case 'a':
                    next = time_string[++index];
                    switch (next) {
                        case 'T':
                        case 't':
                            return 6;
                        default:
                            return -1;
                    }
                case 'U':
                case 'u':
                    next = time_string[++index];
                    switch (next) {
                        case 'N':
                        case 'n':
                            return 0;
                        default:
                            return -1;
                    }
                default:
                    return -1;
            }
        case 'T':
        case 't':
            next = time_string[++index];
            switch (next) {
                case 'H':
                case 'h':
                    next = time_string[++index];
                    switch (next) {
                        case 'U':
                        case 'u':
                            return 4;
                        default:
                            return -1;
                    }
                case 'U':
                case 'u':
                    next = time_string[++index];
                    switch (next) {
                        case 'E':
                        case 'e':
                            return 2;
                        default:
                            return -1;
                    }
                default:
                    return -1;
            }
        case 'M':
        case 'm':
            next = time_string[++index];
            switch (next) {
                case 'O':
                case 'o':
                    next = time_string[++index];
                    switch (next) {
                        case 'N':
                        case 'n':
                            return 1;
                        default:
                            return -1;
                    }
                default:
                    return -1;
            }
        case 'W':
        case 'w':
            next = time_string[++index];
            switch (next) {
                case 'E':
                case 'e':
                    next = time_string[++index];
                    switch (next) {
                        case 'D':
                        case 'd':
                            return 3;
                        default:
                            return -1;
                    }
                default:
                    return -1;
            }
        case 'F':
        case 'f':
            next = time_string[++index];
            switch (next) {
                case 'R':
                case 'r':
                    next = time_string[++index];
                    switch (next) {
                        case 'I':
                        case 'i':
                            return 5;
                        default:
                            return -1;
                    }
                default:
                    return -1;
            }
        default:
            return -1;
    }
}

/* Get the 0-11 monthy number from a string representing Month. Case insensitive and will stop on abbreviation*/
static int get_month_number_from_str(const char *time_string, size_t startIndex, size_t stopIndex) {
    if (stopIndex - startIndex < 3) {
        return -1;
    }

    size_t index = startIndex;

    char c = time_string[index];
    char next = 0;

    /* it's ugly but this should compile down to EXACTLY 3 comparisons and no memory allocations */
    switch (c) {
        case 'M':
        case 'm':
            next = time_string[++index];
            switch (next) {
                case 'A':
                case 'a':
                    next = time_string[++index];
                    switch (next) {
                        case 'Y':
                        case 'y':
                            return 4;
                        case 'R':
                        case 'r':
                            return 2;
                        default:
                            return -1;
                    }
                default:
                    return -1;
            }
        case 'A':
        case 'a':
            next = time_string[++index];
            switch (next) {
                case 'P':
                case 'p':
                    next = time_string[++index];
                    switch (next) {
                        case 'R':
                        case 'r':
                            return 3;
                        default:
                            return -1;
                    }
                case 'U':
                case 'u':
                    next = time_string[++index];
                    switch (next) {
                        case 'G':
                        case 'g':
                            return 7;
                        default:
                            return -1;
                    }
                default:
                    return -1;
            }
        case 'J':
        case 'j':
            next = time_string[++index];
            switch (next) {
                case 'A':
                case 'a':
                    next = time_string[++index];
                    switch (next) {
                        case 'N':
                        case 'n':
                            return 0;
                        default:
                            return -1;
                    }
                case 'U':
                case 'u':
                    next = time_string[++index];
                    switch (next) {
                        case 'N':
                        case 'n':
                            return 5;
                        case 'L':
                        case 'l':
                            return 6;
                        default:
                            return -1;
                    }
                default:
                    return -1;
            }
        case 'F':
        case 'f':
            next = time_string[++index];
            switch (next) {
                case 'E':
                case 'e':
                    next = time_string[++index];
                    switch (next) {
                        case 'B':
                        case 'b':
                            return 1;
                        default:
                            return -1;
                    }
                default:
                    return -1;
            }
        case 'S':
        case 's':
            next = time_string[++index];
            switch (next) {
                case 'E':
                case 'e':
                    next = time_string[++index];
                    switch (next) {
                        case 'P':
                        case 'p':
                            return 8;
                        default:
                            return -1;
                    }
                default:
                    return -1;
            }
        case 'O':
        case 'o':
            next = time_string[++index];
            switch (next) {
                case 'C':
                case 'c':
                    next = time_string[++index];
                    switch (next) {
                        case 'T':
                        case 't':
                            return 9;
                        default:
                            return -1;
                    }
                default:
                    return -1;
            }
        case 'N':
        case 'n':
            next = time_string[++index];
            switch (next) {
                case 'O':
                case 'o':
                    next = time_string[++index];
                    switch (next) {
                        case 'V':
                        case 'v':
                            return 10;
                        default:
                            return -1;
                    }
                default:
                    return -1;
            }
        case 'D':
        case 'd':
            next = time_string[++index];
            switch (next) {
                case 'E':
                case 'e':
                    next = time_string[++index];
                    switch (next) {
                        case 'C':
                        case 'c':
                            return 11;
                        default:
                            return -1;
                    }
                default:
                    return -1;
            }
        default:
            return -1;
    }
}

/* Detects whether or not the passed in timezone string is a UTC zone. */
static bool is_utc_time_zone(const char *str) {
    size_t len = strlen(str);
    if (len < 3) {
        return false;
    }

    int index = 0;
    char c = str[index];
    switch (c) {
        case 'U':
        case 'u':
            c = str[++index];
            switch (c) {
                case 'T':
                case 't':
                    c = str[++index];
                    switch (c) {
                        case 'C':
                        case 'c':
                            return true;
                        default:
                            return false;
                    }

                case 'C':
                case 'c':
                    c = str[++index];
                    switch (c) {
                        case 'T':
                        case 't':
                            return true;
                        default:
                            return false;
                    }
                default:
                    return false;
            }
        case 'G':
        case 'g':
            c = str[++index];
            switch (c) {
                case 'M':
                case 'm':
                    c = str[++index];
                    switch (c) {
                        case 'T':
                        case 't':
                            return true;
                        default:
                            return false;
                    }
                default:
                    return false;
            }
        case '+':
        case '-':
            c = str[++index];
            switch (c) {
                case '0':
                    c = str[++index];
                    switch (c) {
                        case '0':
                            c = str[++index];
                            switch (c) {
                                case '0':
                                    return true;
                                default:
                                    return false;
                            }
                        default:
                            return false;
                    }
                default:
                    return false;
            }
        case 'Z':
            return true;
        default:
            return false;
    }
}

void aws_date_time_init_now(struct aws_date_time *dt) {
    uint64_t current_time = 0;
    aws_sys_clock_get_ticks(&current_time);
    dt->timestamp = aws_timestamp_convert(current_time, AWS_TIMESTAMP_NANOS, AWS_TIMESTAMP_SECS, NULL);
}

void aws_date_time_init_epoch_millis(struct aws_date_time *dt, uint64_t ms_since_epoch) {
    dt->timestamp = ms_since_epoch / AWS_TIMESTAMP_MILLIS;
}

void aws_date_time_init_epoch_secs(struct aws_date_time *dt, double sec_ms) {
    dt->timestamp = (time_t)sec_ms;
}

static int s_parse_iso_8601(const struct aws_byte_buf *date_str, struct tm *parsed_time) {
    size_t index = 0;
    size_t state_start_index = 0;
    const int final_state = 7;
    int state = 0;
    bool error = false;

    while (state <= final_state && !error && index < date_str->len) {
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
    int finalState = 8;
    int state = 0;
    bool error = false;

    while (state <= finalState && !error && index < len) {
        char c = date_str->buffer[index];

        switch (state) {
            case 0:
                if (c == ',') {
                    int weekNumber =
                        get_week_day_number_from_str((const char *)date_str->buffer, state_start_index, index + 1);

                    if (weekNumber > -1) {
                        state = 1;
                        state_start_index = index + 1;
                        parsed_time->tm_wday = weekNumber;
                    } else {
                        error = true;
                    }
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

    return error || state != finalState ? AWS_OP_ERR : AWS_OP_SUCCESS;
}

int aws_date_time_init_from_str(
    struct aws_date_time *dt,
    const struct aws_byte_buf *date_str,
    enum aws_date_format fmt) {
    if (date_str->len > 100) {
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
        dt->timestamp = aws_mk_gm_time(&parsed_time);
    } else {
        dt->timestamp = mktime(&parsed_time);
    }

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

    struct tm time;
    AWS_ZERO_STRUCT(time);
    aws_local_time(dt->timestamp, &time);
    char formatted_string[100];
    AWS_ZERO_ARRAY(formatted_string);

    if (fmt == AWS_DATE_FORMAT_RFC822) {
        strftime(formatted_string, sizeof(formatted_string), RFC822_DATE_FORMAT_STR_WITH_Z, &time);
    } else {
        strftime(formatted_string, sizeof(formatted_string), ISO_8601_LONG_DATE_FORMAT_STR, &time);
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

    struct tm time;
    AWS_ZERO_STRUCT(time);
    aws_gm_time(dt->timestamp, &time);
    char formatted_string[100];
    AWS_ZERO_ARRAY(formatted_string);

    if (fmt == AWS_DATE_FORMAT_RFC822) {
        strftime(formatted_string, sizeof(formatted_string), RFC822_DATE_FORMAT_STR_MINUS_Z, &time);
    } else {
        strftime(formatted_string, sizeof(formatted_string), ISO_8601_LONG_DATE_FORMAT_STR, &time);
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

struct tm s_get_time_struct(struct aws_date_time *dt, bool local_time) {
    struct tm time;
    AWS_ZERO_STRUCT(time);
    if (local_time) {
        aws_local_time(dt->timestamp, &time);
    } else {
        aws_gm_time(dt->timestamp, &time);
    }

    return time;
}

uint16_t aws_date_time_year(struct aws_date_time *dt, bool local_time) {
    struct tm time = s_get_time_struct(dt, local_time);

    return (uint16_t)(time.tm_year + 1900);
}

enum aws_date_month aws_date_time_month(struct aws_date_time *dt, bool local_time) {
    struct tm time = s_get_time_struct(dt, local_time);

    return time.tm_mon;
}

uint8_t aws_date_time_month_day(struct aws_date_time *dt, bool local_time) {
    struct tm time = s_get_time_struct(dt, local_time);

    return (uint8_t)time.tm_mday;
}

enum aws_date_day_of_week aws_date_time_day_of_week(struct aws_date_time *dt, bool local_time) {
    struct tm time = s_get_time_struct(dt, local_time);

    return time.tm_wday;
}

uint8_t aws_date_time_hour(struct aws_date_time *dt, bool local_time) {
    struct tm time = s_get_time_struct(dt, local_time);

    return (uint8_t)time.tm_hour;
}

uint8_t aws_date_time_minute(struct aws_date_time *dt, bool local_time) {
    struct tm time = s_get_time_struct(dt, local_time);

    return (uint8_t)time.tm_min;
}

uint8_t aws_date_time_second(struct aws_date_time *dt, bool local_time) {
    struct tm time = s_get_time_struct(dt, local_time);

    return (uint8_t)time.tm_sec;
}

bool aws_date_time_dst(struct aws_date_time *dt, bool local_time) {
    struct tm time = s_get_time_struct(dt, local_time);

    return time.tm_isdst;
}

int64_t aws_date_time_diff(struct aws_date_time *a, struct aws_date_time *b) {
    return (int64_t)a->timestamp - (int64_t)b->timestamp;
}