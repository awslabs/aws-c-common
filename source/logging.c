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

#include <aws/common/logging.h>

#include <aws/common/string.h>

#include <aws/common/log_channel.h>
#include <aws/common/log_formatter.h>
#include <aws/common/log_writer.h>

#include <stdarg.h>

#if _MSC_VER
#    pragma warning(disable : 4204) /* non-constant aggregate initializer */
#endif

/*
 * Null logger implementation
 */
static enum aws_log_level s_null_logger_get_log_level(struct aws_logger *logger, aws_log_subject_t subject) {
    (void)logger;
    (void)subject;

    return AWS_LL_NONE;
}

static int s_null_logger_log(
    struct aws_logger *logger,
    enum aws_log_level log_level,
    aws_log_subject_t subject,
    const char *format,
    ...) {

    (void)logger;
    (void)log_level;
    (void)subject;
    (void)format;

    return AWS_OP_SUCCESS;
}

static void s_null_logger_clean_up(struct aws_logger *logger) {
    (void)logger;
}

static struct aws_logger_vtable s_null_vtable = {
    .get_log_level = s_null_logger_get_log_level,
    .log = s_null_logger_log,
    .clean_up = s_null_logger_clean_up,
};

static struct aws_logger s_null_logger = {.vtable = &s_null_vtable, .allocator = NULL, .p_impl = NULL};

/*
 * Pipeline logger implementation
 */
static void s_aws_logger_pipeline_owned_clean_up(struct aws_logger *logger) {
    struct aws_logger_pipeline *impl = logger->p_impl;

    AWS_ASSERT(impl->channel->vtable->clean_up != NULL);
    (impl->channel->vtable->clean_up)(impl->channel);

    AWS_ASSERT(impl->formatter->vtable->clean_up != NULL);
    (impl->formatter->vtable->clean_up)(impl->formatter);

    AWS_ASSERT(impl->writer->vtable->clean_up != NULL);
    (impl->writer->vtable->clean_up)(impl->writer);

    aws_mem_release(impl->allocator, impl->channel);
    aws_mem_release(impl->allocator, impl->formatter);
    aws_mem_release(impl->allocator, impl->writer);

    aws_mem_release(impl->allocator, impl);
}

/*
 * Pipeline logger implementation
 */
static int s_aws_logger_pipeline_log(
    struct aws_logger *logger,
    enum aws_log_level log_level,
    aws_log_subject_t subject,
    const char *format,
    ...) {
    va_list format_args;
    va_start(format_args, format);

    struct aws_logger_pipeline *impl = logger->p_impl;
    struct aws_string *output = NULL;

    AWS_ASSERT(impl->formatter->vtable->format != NULL);
    int result = (impl->formatter->vtable->format)(impl->formatter, &output, log_level, subject, format, format_args);

    va_end(format_args);

    if (result != AWS_OP_SUCCESS || output == NULL) {
        return AWS_OP_ERR;
    }

    AWS_ASSERT(impl->channel->vtable->send != NULL);
    if ((impl->channel->vtable->send)(impl->channel, output)) {
        /*
         * failure to send implies failure to transfer ownership
         */
        aws_string_destroy(output);
        return AWS_OP_ERR;
    }

    return AWS_OP_SUCCESS;
}

static enum aws_log_level s_aws_logger_pipeline_get_log_level(struct aws_logger *logger, aws_log_subject_t subject) {
    (void)subject;

    struct aws_logger_pipeline *impl = logger->p_impl;

    return impl->level;
}

struct aws_logger_vtable g_pipeline_logger_owned_vtable = {
    .get_log_level = s_aws_logger_pipeline_get_log_level,
    .log = s_aws_logger_pipeline_log,
    .clean_up = s_aws_logger_pipeline_owned_clean_up,
};

int aws_logger_init_standard(
    struct aws_logger *logger,
    struct aws_allocator *allocator,
    struct aws_logger_standard_options *options) {

    struct aws_logger_pipeline *impl = aws_mem_calloc(allocator, 1, sizeof(struct aws_logger_pipeline));
    if (impl == NULL) {
        return AWS_OP_ERR;
    }

    struct aws_log_writer *writer = aws_mem_acquire(allocator, sizeof(struct aws_log_writer));
    if (writer == NULL) {
        goto on_allocate_writer_failure;
    }

    struct aws_log_writer_file_options file_writer_options = {
        .filename = options->filename,
        .file = options->file,
    };

    if (aws_log_writer_init_file(writer, allocator, &file_writer_options)) {
        goto on_init_writer_failure;
    }

    struct aws_log_formatter *formatter = aws_mem_acquire(allocator, sizeof(struct aws_log_formatter));
    if (formatter == NULL) {
        goto on_allocate_formatter_failure;
    }

    struct aws_log_formatter_standard_options formatter_options = {.date_format = AWS_DATE_FORMAT_ISO_8601};

    if (aws_log_formatter_init_default(formatter, allocator, &formatter_options)) {
        goto on_init_formatter_failure;
    }

    struct aws_log_channel *channel = aws_mem_acquire(allocator, sizeof(struct aws_log_channel));
    if (channel == NULL) {
        goto on_allocate_channel_failure;
    }

    if (aws_log_channel_init_background(channel, allocator, writer) == AWS_OP_SUCCESS) {
        impl->formatter = formatter;
        impl->channel = channel;
        impl->writer = writer;
        impl->allocator = allocator;
        impl->level = options->level;

        logger->vtable = &g_pipeline_logger_owned_vtable;
        logger->allocator = allocator;
        logger->p_impl = impl;

        return AWS_OP_SUCCESS;
    }

    aws_mem_release(allocator, channel);

on_allocate_channel_failure:
    aws_log_formatter_clean_up(formatter);

on_init_formatter_failure:
    aws_mem_release(allocator, formatter);

on_allocate_formatter_failure:
    aws_log_writer_clean_up(writer);

on_init_writer_failure:
    aws_mem_release(allocator, writer);

on_allocate_writer_failure:
    aws_mem_release(allocator, impl);

    return AWS_OP_ERR;
}

/*
 * Pipeline logger implementation where all the components are externally owned.  No clean up
 * is done on the components.  Useful for tests where components are on the stack and often mocked.
 */
static void s_aws_pipeline_logger_unowned_clean_up(struct aws_logger *logger) {
    struct aws_logger_pipeline *impl = (struct aws_logger_pipeline *)logger->p_impl;

    aws_mem_release(impl->allocator, impl);
}

static struct aws_logger_vtable s_pipeline_logger_unowned_vtable = {
    .get_log_level = s_aws_logger_pipeline_get_log_level,
    .log = s_aws_logger_pipeline_log,
    .clean_up = s_aws_pipeline_logger_unowned_clean_up,
};

int aws_logger_init_from_external(
    struct aws_logger *logger,
    struct aws_allocator *allocator,
    struct aws_log_formatter *formatter,
    struct aws_log_channel *channel,
    struct aws_log_writer *writer,
    enum aws_log_level level) {

    struct aws_logger_pipeline *impl = aws_mem_acquire(allocator, sizeof(struct aws_logger_pipeline));

    if (impl == NULL) {
        return AWS_OP_ERR;
    }

    impl->formatter = formatter;
    impl->channel = channel;
    impl->writer = writer;
    impl->allocator = allocator;
    impl->level = level;

    logger->vtable = &s_pipeline_logger_unowned_vtable;
    logger->allocator = allocator;
    logger->p_impl = impl;

    return AWS_OP_SUCCESS;
}

/*
 * Global API
 */
static struct aws_logger *s_root_logger_ptr = &s_null_logger;

void aws_logger_set(struct aws_logger *logger) {
    if (logger != NULL) {
        s_root_logger_ptr = logger;
    } else {
        s_root_logger_ptr = &s_null_logger;
    }
}

struct aws_logger *aws_logger_get(void) {
    return s_root_logger_ptr;
}

void aws_logger_clean_up(struct aws_logger *logger) {
    AWS_ASSERT(logger->vtable->clean_up != NULL);

    logger->vtable->clean_up(logger);
}

static const char *s_log_level_strings[AWS_LL_COUNT] = {"NONE ", "FATAL", "ERROR", "WARN ", "INFO ", "DEBUG", "TRACE"};

int aws_log_level_to_string(enum aws_log_level log_level, const char **level_string) {
    AWS_ERROR_PRECONDITION(log_level < AWS_LL_COUNT);

    if (level_string != NULL) {
        *level_string = s_log_level_strings[log_level];
    }

    return AWS_OP_SUCCESS;
}

#ifndef AWS_MAX_LOG_SUBJECT_SLOTS
#    define AWS_MAX_LOG_SUBJECT_SLOTS 16u
#endif

static const uint32_t S_MAX_LOG_SUBJECT = AWS_LOG_SUBJECT_SPACE_SIZE * AWS_MAX_LOG_SUBJECT_SLOTS - 1;

static const struct aws_log_subject_info_list *volatile s_log_subject_slots[AWS_MAX_LOG_SUBJECT_SLOTS] = {0};

static const struct aws_log_subject_info *s_get_log_subject_info_by_id(aws_log_subject_t subject) {
    if (subject > S_MAX_LOG_SUBJECT) {
        return NULL;
    }

    uint32_t slot_index = subject >> AWS_LOG_SUBJECT_BIT_SPACE;
    uint32_t subject_index = subject & AWS_LOG_SUBJECT_SPACE_MASK;

    const struct aws_log_subject_info_list *subject_slot = s_log_subject_slots[slot_index];

    if (!subject_slot || subject_index >= subject_slot->count) {
        return NULL;
    }

    return &subject_slot->subject_list[subject_index];
}

const char *aws_log_subject_name(aws_log_subject_t subject) {
    const struct aws_log_subject_info *subject_info = s_get_log_subject_info_by_id(subject);

    if (subject_info != NULL) {
        return subject_info->subject_name;
    }

    return "Unknown";
}

void aws_register_log_subject_info_list(struct aws_log_subject_info_list *log_subject_list) {
    (void)log_subject_list;

    /*
     * We're not so worried about these asserts being removed in an NDEBUG build
     * - we'll either segfault immediately (for the first two) or for the count
     * assert, the registration will be ineffective.
     */
    AWS_ASSERT(log_subject_list);
    AWS_ASSERT(log_subject_list->subject_list);
    AWS_ASSERT(log_subject_list->count);

    uint32_t min_range = log_subject_list->subject_list[0].subject_id;

    uint32_t slot_index = min_range >> AWS_LOG_SUBJECT_BIT_SPACE;

    AWS_ASSERT(slot_index < AWS_MAX_LOG_SUBJECT_SLOTS);

    if (slot_index >= AWS_MAX_LOG_SUBJECT_SLOTS) {
        /* This is an NDEBUG build apparently. Kill the process rather than
         * corrupting heap. */
        fprintf(stderr, "Bad log subject slot index 0x%016x\n", slot_index);
        abort();
    }

    s_log_subject_slots[slot_index] = log_subject_list;
}

static struct aws_log_subject_info s_common_log_subject_infos[] = {
    DEFINE_LOG_SUBJECT_INFO(
        AWS_LS_COMMON_GENERAL,
        "aws-c-common",
        "Subject for aws-c-common logging that doesn't belong to any particular category"),
    DEFINE_LOG_SUBJECT_INFO(
        AWS_LS_COMMON_TASK_SCHEDULER,
        "task-scheduler",
        "Subject for task scheduler or task specific logging."),
};

static struct aws_log_subject_info_list s_common_log_subject_list = {
    .subject_list = s_common_log_subject_infos,
    .count = AWS_ARRAY_SIZE(s_common_log_subject_infos),
};

void aws_common_load_log_subject_strings(void) {
    aws_register_log_subject_info_list(&s_common_log_subject_list);
}
