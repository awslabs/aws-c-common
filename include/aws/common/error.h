#ifndef AWS_COMMON_ERROR_H
#define AWS_COMMON_ERROR_H

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

#include <aws/common/assert.h>
#include <aws/common/exports.h>
#include <aws/common/macros.h>
#include <aws/common/stdint.h>

#define AWS_OP_SUCCESS (0)
#define AWS_OP_ERR (-1)

struct aws_error_info {
    int error_code;
    const char *literal_name;
    const char *error_str;
    const char *lib_name;
    const char *formatted_name;
};

struct aws_error_info_list {
    const struct aws_error_info *error_list;
    uint16_t count;
};

#define AWS_DEFINE_ERROR_INFO(C, ES, LN)                                                                               \
    {                                                                                                                  \
        .literal_name = #C, .error_code = (C), .error_str = (ES), .lib_name = (LN),                                    \
        .formatted_name = LN ": " #C ", " ES,                                                                          \
    }

typedef void(aws_error_handler_fn)(int err, void *ctx);

AWS_EXTERN_C_BEGIN

/*
 * Returns the latest error code on the current thread, or 0 if none have
 * occurred.
 */
AWS_COMMON_API
int aws_last_error(void);

/*
 * Returns the error str corresponding to `err`.
 */
AWS_COMMON_API
const char *aws_error_str(int err);

/*
 * Returns the enum name corresponding to `err`.
 */
AWS_COMMON_API
const char *aws_error_name(int err);

/*
 * Returns the error lib name corresponding to `err`.
 */
AWS_COMMON_API
const char *aws_error_lib_name(int err);

/*
 * Returns libname concatenated with error string.
 */
AWS_COMMON_API
const char *aws_error_debug_str(int err);

/*
 * Internal implementation detail.
 */
AWS_COMMON_API
void aws_raise_error_private(int err);

/*
 * Raises `err` to the installed callbacks, and sets the thread's error.
 */
AWS_STATIC_IMPL
int aws_raise_error(int err);

/*
 * Resets the `err` back to defaults
 */
AWS_COMMON_API
void aws_reset_error(void);
/*
 * Sets `err` to the latest error. Does not invoke callbacks.
 */
AWS_COMMON_API
void aws_restore_error(int err);

/*
 * Sets an application wide error handler function. This will be overridden by
 * the thread local handler. The previous handler is returned, this can be used
 * for restoring an error handler if it needs to be overridden temporarily.
 * Setting this to NULL will turn off this error callback after it has been
 * enabled.
 */
AWS_COMMON_API
aws_error_handler_fn *aws_set_global_error_handler_fn(aws_error_handler_fn *handler, void *ctx);

/*
 * Sets a thread-local error handler function. This will override the global
 * handler. The previous handler is returned, this can be used for restoring an
 * error handler if it needs to be overridden temporarily. Setting this to NULL
 * will turn off this error callback after it has been enabled.
 */
AWS_COMMON_API
aws_error_handler_fn *aws_set_thread_local_error_handler_fn(aws_error_handler_fn *handler, void *ctx);

/** TODO: this needs to be a private function (wait till we have the cmake story
 * better before moving it though). It should be external for the purpose of
 * other libs we own, but customers should not be able to hit it without going
 * out of their way to do so.
 */
AWS_COMMON_API
void aws_register_error_info(const struct aws_error_info_list *error_info);

AWS_COMMON_API
void aws_unregister_error_info(const struct aws_error_info_list *error_info);

/**
 * Convert a c library io error into an aws error.
 */
AWS_COMMON_API
int aws_translate_and_raise_io_error(int error_no);

#ifndef AWS_NO_STATIC_IMPL
#    include <aws/common/error.inl>
#endif /* AWS_NO_STATIC_IMPL */

AWS_EXTERN_C_END

enum aws_common_error {
    AWS_ERROR_SUCCESS = 0,
    AWS_ERROR_OOM,
    AWS_ERROR_UNKNOWN,
    AWS_ERROR_SHORT_BUFFER,
    AWS_ERROR_OVERFLOW_DETECTED,
    AWS_ERROR_UNSUPPORTED_OPERATION,
    AWS_ERROR_INVALID_BUFFER_SIZE,
    AWS_ERROR_INVALID_HEX_STR,
    AWS_ERROR_INVALID_BASE64_STR,
    AWS_ERROR_INVALID_INDEX,
    AWS_ERROR_THREAD_INVALID_SETTINGS,
    AWS_ERROR_THREAD_INSUFFICIENT_RESOURCE,
    AWS_ERROR_THREAD_NO_PERMISSIONS,
    AWS_ERROR_THREAD_NOT_JOINABLE,
    AWS_ERROR_THREAD_NO_SUCH_THREAD_ID,
    AWS_ERROR_THREAD_DEADLOCK_DETECTED,
    AWS_ERROR_MUTEX_NOT_INIT,
    AWS_ERROR_MUTEX_TIMEOUT,
    AWS_ERROR_MUTEX_CALLER_NOT_OWNER,
    AWS_ERROR_MUTEX_FAILED,
    AWS_ERROR_COND_VARIABLE_INIT_FAILED,
    AWS_ERROR_COND_VARIABLE_TIMED_OUT,
    AWS_ERROR_COND_VARIABLE_ERROR_UNKNOWN,
    AWS_ERROR_CLOCK_FAILURE,
    AWS_ERROR_LIST_EMPTY,
    AWS_ERROR_DEST_COPY_TOO_SMALL,
    AWS_ERROR_LIST_EXCEEDS_MAX_SIZE,
    AWS_ERROR_LIST_STATIC_MODE_CANT_SHRINK,
    AWS_ERROR_PRIORITY_QUEUE_FULL,
    AWS_ERROR_PRIORITY_QUEUE_EMPTY,
    AWS_ERROR_PRIORITY_QUEUE_BAD_NODE,
    AWS_ERROR_HASHTBL_ITEM_NOT_FOUND,
    AWS_ERROR_INVALID_DATE_STR,
    AWS_ERROR_INVALID_ARGUMENT,
    AWS_ERROR_RANDOM_GEN_FAILED,
    AWS_ERROR_MALFORMED_INPUT_STRING,
    AWS_ERROR_UNIMPLEMENTED,
    AWS_ERROR_INVALID_STATE,
    AWS_ERROR_ENVIRONMENT_GET,
    AWS_ERROR_ENVIRONMENT_SET,
    AWS_ERROR_ENVIRONMENT_UNSET,
    AWS_ERROR_STREAM_UNSEEKABLE,
    AWS_ERROR_NO_PERMISSION,
    AWS_ERROR_FILE_INVALID_PATH,
    AWS_ERROR_MAX_FDS_EXCEEDED,
    AWS_ERROR_SYS_CALL_FAILURE,
    AWS_ERROR_C_STRING_BUFFER_NOT_NULL_TERMINATED,
    AWS_ERROR_STRING_MATCH_NOT_FOUND,

    AWS_ERROR_END_COMMON_RANGE = 0x03FF
};

#endif /* AWS_COMMON_ERROR_H */
