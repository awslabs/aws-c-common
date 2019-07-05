/*
 * Copyright 2010-2019 Amazon.com, Inc. or its affiliates. All Rights Reserved.
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

#include <aws/common/log_formatter.h>

#include <aws/common/date_time.h>
#include <aws/common/string.h>
#include <aws/common/thread.h>

#include <inttypes.h>
#include <stdarg.h>

/*
 * Default formatter implementation
 */

#if _MSC_VER
#    pragma warning(disable : 4204) /* non-constant aggregate initializer */
#endif

/* (max) strlen of "[<LogLevel>]" */
#define LOG_LEVEL_PREFIX_PADDING 7

/* (max) strlen of "[<ThreadId>]" */
#define THREAD_ID_PREFIX_PADDING 22

/* strlen of (user-content separator) " - " + "\n" + spaces between prefix fields + brackets around timestamp + 1 +
   subject_name padding */
#define MISC_PADDING 15

#define MAX_LOG_LINE_PREFIX_SIZE                                                                                       \
    (LOG_LEVEL_PREFIX_PADDING + THREAD_ID_PREFIX_PADDING + MISC_PADDING + AWS_DATE_TIME_STR_MAX_LEN)

struct aws_default_log_formatter_impl {
    enum aws_date_format date_format;
};

static int s_default_aws_log_formatter_format(
    struct aws_log_formatter *formatter,
    struct aws_string **formatted_output,
    enum aws_log_level level,
    aws_log_subject_t subject,
    const char *format,
    va_list args) {

    (void)subject;

    struct aws_default_log_formatter_impl *impl = formatter->impl;

    if (formatted_output == NULL) {
        return AWS_OP_ERR;
    }

    /*
     * Calculate how much room we'll need to build the full log line.
     * You cannot consume a va_list twice, so we have to copy it.
     */
    va_list tmp_args;
    va_copy(tmp_args, args);
#ifdef WIN32
    int required_length = _vscprintf(format, tmp_args) + 1;
#else
    int required_length = vsnprintf(NULL, 0, format, tmp_args) + 1;
#endif
    va_end(tmp_args);

    /*
     * Allocate enough room to hold the line.  Then we'll (unsafely) do formatted IO directly into the aws_string
     * memory.
     */
    const char *subject_name = aws_log_subject_name(subject);
    int subject_name_len = 0;

    if (subject_name) {
        subject_name_len = (int)strlen(subject_name);
    }

    int total_length = required_length + MAX_LOG_LINE_PREFIX_SIZE + subject_name_len;
    struct aws_string *raw_string = aws_mem_calloc(formatter->allocator, 1, sizeof(struct aws_string) + total_length);
    if (raw_string == NULL) {
        goto error_clean_up;
    }

    char *log_line_buffer = (char *)raw_string->bytes;
    size_t current_index = 0;

    /*
     * Begin the log line with "[<Log Level>] ["
     */
    const char *level_string = NULL;
    if (aws_log_level_to_string(level, &level_string)) {
        goto error_clean_up;
    }

    int log_level_length = snprintf(log_line_buffer, total_length, "[%s] [", level_string);
    if (log_level_length < 0) {
        goto error_clean_up;
    }

    current_index += log_level_length;

    /*
     * Add the timestamp.  To avoid copies and allocations, do some byte buffer tomfoolery.
     *
     * First, make a byte_buf that points to the current position in the output string
     */
    struct aws_byte_buf timestamp_buffer = {.allocator = formatter->allocator,
                                            .buffer = (uint8_t *)log_line_buffer + current_index,
                                            .capacity = total_length - current_index,
                                            .len = 0};

    /*
     * Output the current time to the byte_buf
     */
    struct aws_date_time current_time;
    aws_date_time_init_now(&current_time);

    int result = aws_date_time_to_utc_time_str(&current_time, impl->date_format, &timestamp_buffer);
    if (result != AWS_OP_SUCCESS) {
        goto error_clean_up;
    }

    current_index += timestamp_buffer.len;

    /*
     * Add thread id and user content separator (" - ")
     */
    uint64_t current_thread_id = aws_thread_current_thread_id();
    int thread_id_written =
        snprintf(log_line_buffer + current_index, total_length - current_index, "] [%" PRIu64 "] ", current_thread_id);
    if (thread_id_written < 0) {
        goto error_clean_up;
    }

    current_index += thread_id_written;

    /* output subject name */
    if (subject_name) {
        int subject_written =
            snprintf(log_line_buffer + current_index, total_length - current_index, "[%s]", subject_name);

        if (subject_written < 0) {
            goto error_clean_up;
        }

        current_index += subject_written;
    }

    current_index += snprintf(log_line_buffer + current_index, total_length - current_index, " - ");

    /*
     * Now write the actual data requested by the user
     */
#ifdef WIN32
    int written_count =
        vsnprintf_s(log_line_buffer + current_index, total_length - current_index, _TRUNCATE, format, args);
#else
    int written_count = vsnprintf(log_line_buffer + current_index, total_length - current_index, format, args);
#endif /* WIN32 */
    if (written_count < 0) {
        goto error_clean_up;
    }

    /*
     * End with a newline.
     */
    current_index += written_count;
    written_count = snprintf(log_line_buffer + current_index, total_length - current_index, "\n");
    if (written_count < 0) {
        goto error_clean_up;
    }

    *(struct aws_allocator **)(&raw_string->allocator) = formatter->allocator;
    *(size_t *)(&raw_string->len) = current_index + written_count;

    *formatted_output = raw_string;

    return AWS_OP_SUCCESS;

error_clean_up:

    if (raw_string != NULL) {
        aws_mem_release(formatter->allocator, raw_string);
    }

    return AWS_OP_ERR;
}

static void s_default_aws_log_formatter_clean_up(struct aws_log_formatter *formatter) {
    aws_mem_release(formatter->allocator, formatter->impl);
}

static struct aws_log_formatter_vtable s_default_log_formatter_vtable = {
    .format = s_default_aws_log_formatter_format,
    .clean_up = s_default_aws_log_formatter_clean_up,
};

int aws_log_formatter_init_default(
    struct aws_log_formatter *formatter,
    struct aws_allocator *allocator,
    struct aws_log_formatter_standard_options *options) {
    struct aws_default_log_formatter_impl *impl =
        aws_mem_calloc(allocator, 1, sizeof(struct aws_default_log_formatter_impl));
    impl->date_format = options->date_format;

    formatter->vtable = &s_default_log_formatter_vtable;
    formatter->allocator = allocator;
    formatter->impl = impl;

    return AWS_OP_SUCCESS;
}

void aws_log_formatter_clean_up(struct aws_log_formatter *formatter) {
    AWS_ASSERT(formatter->vtable->clean_up);
    (formatter->vtable->clean_up)(formatter);
}
