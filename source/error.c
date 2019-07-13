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

#include <aws/common/error.h>

#include <aws/common/common.h>

#include <errno.h>
#include <stdio.h>
#include <stdlib.h>

static AWS_THREAD_LOCAL int tl_last_error = 0;

static aws_error_handler_fn *s_global_handler = NULL;
static void *s_global_error_context = NULL;

static AWS_THREAD_LOCAL aws_error_handler_fn *tl_thread_handler = NULL;
AWS_THREAD_LOCAL void *tl_thread_handler_context = NULL;

#ifndef AWS_MAX_ERROR_SLOTS
#    define AWS_MAX_ERROR_SLOTS 16
#endif

/* Since slot size is 00000100 00000000, to divide, we need to shift right by 10
 * bits to find the slot, and to find the modulus, we use a binary and with
 * 00000011 11111111 to find the index in that slot. The next three values
 * define those constants */
#define AWS_ERROR_SLOT_SIZE 0x0400
#define SLOT_DIV_SHIFT 0x0A
#define SLOT_MASK 0x03FF

static const int MAX_ERROR_CODE = AWS_ERROR_SLOT_SIZE * AWS_MAX_ERROR_SLOTS;

static const struct aws_error_info_list *volatile ERROR_SLOTS[AWS_MAX_ERROR_SLOTS] = {0};

int aws_last_error(void) {
    return tl_last_error;
}

static const struct aws_error_info *get_error_by_code(int err) {
    if (err >= MAX_ERROR_CODE || err < 0) {
        return NULL;
    }

    int slot_index = err >> SLOT_DIV_SHIFT;
    int error_index = err & SLOT_MASK;

    const struct aws_error_info_list *error_slot = ERROR_SLOTS[slot_index];

    if (!error_slot || error_index >= error_slot->count) {
        return NULL;
    }

    return &error_slot->error_list[error_index];
}

const char *aws_error_str(int err) {
    const struct aws_error_info *error_info = get_error_by_code(err);

    if (error_info) {
        return error_info->error_str;
    }

    return "Unknown Error Code";
}

const char *aws_error_name(int err) {
    const struct aws_error_info *error_info = get_error_by_code(err);

    if (error_info) {
        return error_info->literal_name;
    }

    return "Unknown Error Code";
}

const char *aws_error_lib_name(int err) {
    const struct aws_error_info *error_info = get_error_by_code(err);

    if (error_info) {
        return error_info->lib_name;
    }

    return "Unknown Error Code";
}

const char *aws_error_debug_str(int err) {
    const struct aws_error_info *error_info = get_error_by_code(err);

    if (error_info) {
        return error_info->formatted_name;
    }

    return "Unknown Error Code";
}

void aws_raise_error_private(int err) {
    tl_last_error = err;

    if (tl_thread_handler) {
        tl_thread_handler(tl_last_error, tl_thread_handler_context);
    } else if (s_global_handler) {
        s_global_handler(tl_last_error, s_global_error_context);
    }
}

void aws_reset_error(void) {
    tl_last_error = 0;
}

void aws_restore_error(int err) {
    tl_last_error = err;
}

aws_error_handler_fn *aws_set_global_error_handler_fn(aws_error_handler_fn *handler, void *ctx) {
    aws_error_handler_fn *old_handler = s_global_handler;
    s_global_handler = handler;
    s_global_error_context = ctx;

    return old_handler;
}

aws_error_handler_fn *aws_set_thread_local_error_handler_fn(aws_error_handler_fn *handler, void *ctx) {
    aws_error_handler_fn *old_handler = tl_thread_handler;
    tl_thread_handler = handler;
    tl_thread_handler_context = ctx;

    return old_handler;
}

void aws_register_error_info(const struct aws_error_info_list *error_info) {
    /*
     * We're not so worried about these asserts being removed in an NDEBUG build
     * - we'll either segfault immediately (for the first two) or for the count
     * assert, the registration will be ineffective.
     */
    AWS_ASSERT(error_info);
    AWS_ASSERT(error_info->error_list);
    AWS_ASSERT(error_info->count);

    int min_range = error_info->error_list[0].error_code;

    int slot_index = min_range >> SLOT_DIV_SHIFT;

    AWS_ASSERT(slot_index < AWS_MAX_ERROR_SLOTS && slot_index >= 0);

    if (slot_index >= AWS_MAX_ERROR_SLOTS || slot_index < 0) {
        /* This is an NDEBUG build apparently. Kill the process rather than
         * corrupting heap. */
        fprintf(stderr, "Bad error slot index 0x%016x\n", slot_index);
        abort();
    }

#if DEBUG_BUILD
    /* Assert that error info entries are in the right order. */
    for (int i = 1; i < error_info->count; ++i) {
        int expected_code = min_range + i;
        if (error_info->error_list[i].error_code != expected_code) {
            fprintf(stderr, "Error %s is at wrong index of error info list.\n", error_info->error_list[i].literal_name);
            abort();
        }
    }
#endif /* DEBUG_BUILD */

    ERROR_SLOTS[slot_index] = error_info;
}

static int8_t s_error_strings_loaded = 0;

#define AWS_DEFINE_ERROR_INFO_COMMON(C, ES) [C - 0x0000] = AWS_DEFINE_ERROR_INFO(C, ES, "libaws-c-common")

/* clang-format off */
static struct aws_error_info errors[] = {
    AWS_DEFINE_ERROR_INFO_COMMON(
        AWS_ERROR_SUCCESS,
        "Success."),
    AWS_DEFINE_ERROR_INFO_COMMON(
        AWS_ERROR_OOM,
        "Out of memory."),
    AWS_DEFINE_ERROR_INFO_COMMON(
        AWS_ERROR_UNKNOWN,
        "Unknown error."),
    AWS_DEFINE_ERROR_INFO_COMMON(
        AWS_ERROR_SHORT_BUFFER,
        "Buffer is not large enough to hold result."),
    AWS_DEFINE_ERROR_INFO_COMMON(
        AWS_ERROR_OVERFLOW_DETECTED,
        "Fixed size value overflow was detected."),
    AWS_DEFINE_ERROR_INFO_COMMON(
        AWS_ERROR_UNSUPPORTED_OPERATION,
        "Unsupported operation."),
    AWS_DEFINE_ERROR_INFO_COMMON(
        AWS_ERROR_INVALID_BUFFER_SIZE,
        "Invalid buffer size."),
    AWS_DEFINE_ERROR_INFO_COMMON(
        AWS_ERROR_INVALID_HEX_STR,
        "Invalid hex string."),
    AWS_DEFINE_ERROR_INFO_COMMON(
        AWS_ERROR_INVALID_BASE64_STR,
        "Invalid base64 string."),
    AWS_DEFINE_ERROR_INFO_COMMON(
        AWS_ERROR_INVALID_INDEX,
        "Invalid index for list access."),
    AWS_DEFINE_ERROR_INFO_COMMON(
        AWS_ERROR_THREAD_INVALID_SETTINGS,
        "Invalid thread settings."),
    AWS_DEFINE_ERROR_INFO_COMMON(
        AWS_ERROR_THREAD_INSUFFICIENT_RESOURCE,
        "Insufficent resources for thread."),
    AWS_DEFINE_ERROR_INFO_COMMON(
        AWS_ERROR_THREAD_NO_PERMISSIONS,
        "Insufficient permissions for thread operation."),
    AWS_DEFINE_ERROR_INFO_COMMON(
        AWS_ERROR_THREAD_NOT_JOINABLE,
        "Thread not joinable."),
    AWS_DEFINE_ERROR_INFO_COMMON(
        AWS_ERROR_THREAD_NO_SUCH_THREAD_ID,
        "No such thread ID."),
    AWS_DEFINE_ERROR_INFO_COMMON(
        AWS_ERROR_THREAD_DEADLOCK_DETECTED,
        "Deadlock detected in thread."),
    AWS_DEFINE_ERROR_INFO_COMMON(
        AWS_ERROR_MUTEX_NOT_INIT,
        "Mutex not initialized."),
    AWS_DEFINE_ERROR_INFO_COMMON(
        AWS_ERROR_MUTEX_TIMEOUT,
        "Mutex operation timed out."),
    AWS_DEFINE_ERROR_INFO_COMMON(
        AWS_ERROR_MUTEX_CALLER_NOT_OWNER,
        "The caller of a mutex operation was not the owner."),
    AWS_DEFINE_ERROR_INFO_COMMON(
        AWS_ERROR_MUTEX_FAILED,
        "Mutex operation failed."),
    AWS_DEFINE_ERROR_INFO_COMMON(
        AWS_ERROR_COND_VARIABLE_INIT_FAILED,
        "Condition variable initialization failed."),
    AWS_DEFINE_ERROR_INFO_COMMON(
        AWS_ERROR_COND_VARIABLE_TIMED_OUT,
        "Condition variable wait timed out."),
    AWS_DEFINE_ERROR_INFO_COMMON(
        AWS_ERROR_COND_VARIABLE_ERROR_UNKNOWN,
        "Condition variable unknown error."),
    AWS_DEFINE_ERROR_INFO_COMMON(
        AWS_ERROR_CLOCK_FAILURE,
        "Clock operation failed."),
    AWS_DEFINE_ERROR_INFO_COMMON(
        AWS_ERROR_LIST_EMPTY,
        "Empty list."),
    AWS_DEFINE_ERROR_INFO_COMMON(
        AWS_ERROR_DEST_COPY_TOO_SMALL,
        "Destination of copy is too small."),
    AWS_DEFINE_ERROR_INFO_COMMON(
        AWS_ERROR_LIST_EXCEEDS_MAX_SIZE,
        "A requested operation on a list would exceed it's max size."),
    AWS_DEFINE_ERROR_INFO_COMMON(
        AWS_ERROR_LIST_STATIC_MODE_CANT_SHRINK,
        "Attempt to shrink a list in static mode."),
    AWS_DEFINE_ERROR_INFO_COMMON(
        AWS_ERROR_PRIORITY_QUEUE_FULL,
        "Attempt to add items to a full preallocated queue in static mode."),
    AWS_DEFINE_ERROR_INFO_COMMON(
        AWS_ERROR_PRIORITY_QUEUE_EMPTY,
        "Attempt to pop an item from an empty queue."),
    AWS_DEFINE_ERROR_INFO_COMMON(
        AWS_ERROR_PRIORITY_QUEUE_BAD_NODE,
        "Bad node handle passed to remove."),
    AWS_DEFINE_ERROR_INFO_COMMON(
        AWS_ERROR_HASHTBL_ITEM_NOT_FOUND,
        "Item not found in hash table."),
    AWS_DEFINE_ERROR_INFO_COMMON(
        AWS_ERROR_INVALID_DATE_STR,
        "Date string is invalid and cannot be parsed."
    ),
    AWS_DEFINE_ERROR_INFO_COMMON(
        AWS_ERROR_INVALID_ARGUMENT,
        "An invalid argument was passed to a function."
    ),
    AWS_DEFINE_ERROR_INFO_COMMON(
        AWS_ERROR_RANDOM_GEN_FAILED,
        "A call to the random number generator failed. Retry later."
    ),
    AWS_DEFINE_ERROR_INFO_COMMON(
        AWS_ERROR_MALFORMED_INPUT_STRING,
        "An input string was passed to a parser and the string was incorrectly formatted."
    ),
    AWS_DEFINE_ERROR_INFO_COMMON(
        AWS_ERROR_UNIMPLEMENTED,
        "A function was called, but is not implemented."
    ),
    AWS_DEFINE_ERROR_INFO_COMMON(
        AWS_ERROR_INVALID_STATE,
        "An invalid state was encountered."
    ),
    AWS_DEFINE_ERROR_INFO_COMMON(
        AWS_ERROR_ENVIRONMENT_GET,
        "System call failure when getting an environment variable."
    ),
    AWS_DEFINE_ERROR_INFO_COMMON(
        AWS_ERROR_ENVIRONMENT_SET,
        "System call failure when setting an environment variable."
    ),
    AWS_DEFINE_ERROR_INFO_COMMON(
        AWS_ERROR_ENVIRONMENT_UNSET,
        "System call failure when unsetting an environment variable."
    ),
    AWS_DEFINE_ERROR_INFO_COMMON(
        AWS_ERROR_SYS_CALL_FAILURE,
        "System call failure"),
    AWS_DEFINE_ERROR_INFO_COMMON(
        AWS_ERROR_FILE_INVALID_PATH,
        "Invalid file path."),
    AWS_DEFINE_ERROR_INFO_COMMON(
        AWS_ERROR_MAX_FDS_EXCEEDED,
        "The maximum number of fds has been exceeded."),
    AWS_DEFINE_ERROR_INFO_COMMON(
        AWS_ERROR_NO_PERMISSION,
        "User does not have permission to perform the requested action."),
    AWS_DEFINE_ERROR_INFO_COMMON(
        AWS_ERROR_STREAM_UNSEEKABLE,
        "Stream does not support seek operations"),
};
/* clang-format on */

static struct aws_error_info_list s_list = {
    .error_list = errors,
    .count = AWS_ARRAY_SIZE(errors),
};

void aws_load_error_strings(void) {
    if (!s_error_strings_loaded) {
        s_error_strings_loaded = 1;
        aws_register_error_info(&s_list);
    }
}

int aws_translate_and_raise_io_error(int error_no) {
    switch (error_no) {
        case EINVAL:
            return aws_raise_error(AWS_ERROR_INVALID_ARGUMENT);
        case ESPIPE:
            return aws_raise_error(AWS_ERROR_STREAM_UNSEEKABLE);
        case EPERM:
        case EACCES:
            return aws_raise_error(AWS_ERROR_NO_PERMISSION);
        case EISDIR:
        case ENAMETOOLONG:
        case ENOENT:
            return aws_raise_error(AWS_ERROR_FILE_INVALID_PATH);
        case ENFILE:
            return aws_raise_error(AWS_ERROR_MAX_FDS_EXCEEDED);
        case ENOMEM:
            return aws_raise_error(AWS_ERROR_OOM);
        default:
            return aws_raise_error(AWS_ERROR_SYS_CALL_FAILURE);
    }
}
