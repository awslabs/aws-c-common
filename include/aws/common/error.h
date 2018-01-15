#ifndef AWS_COMMON_ERROR_H_

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

#define AWS_COMMON_ERROR_H_

#include <aws/common/exports.h>
#include <stdint.h>

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

#define AWS_DEFINE_ERROR_INFO(NAME, C, ES, LN)                                                                         \
{                                                                                                                      \
    .literal_name = #C,                                                                                                \
    .error_code = C,                                                                                                   \
    .error_str = ES,                                                                                                   \
    .lib_name = LN,                                                                                                    \
    .formatted_name = LN ": " #C ", " ES                                                                               \
}

typedef void(*aws_error_handler)(int err, void *ctx);

#ifdef __cplusplus
extern "C" {
#endif

/*
 * Returns the latest error code on the current thread, or 0 if none have occurred.
 */
AWS_COMMON_API int aws_last_error(void);

/*
 * Returns the error str corresponding to `err`.
 */
AWS_COMMON_API const char *aws_error_str(int err);

/*
 * Returns the error lib name corresponding to `err`.
 */
AWS_COMMON_API const char *aws_error_lib_name(int err);

/*
 * Returns libname concatenated with error string.
 */
AWS_COMMON_API const char *aws_error_debug_str(int err);

/*
 * Raises `err` to the installed callbacks, and sets the thread's error.
 */
AWS_COMMON_API void aws_raise_error(int err);
/*
 * Resets the `err` back to defaults
 */
AWS_COMMON_API void aws_reset_error(void);
/*
 * Sets `err` to the latest error. Does not invoke callbacks.
 */
AWS_COMMON_API void aws_restore_error(int err);

/*
 * Sets an application wide error handler function. This will be overridden by the thread local handler
 */
AWS_COMMON_API void aws_set_global_error_handler_fn(aws_error_handler handler, void *ctx);

/*
 * Sets a thread-local error handler function. This will override the global handler.
 */
AWS_COMMON_API void aws_set_thread_local_error_handler_fn(aws_error_handler handler, void *ctx);

/** TODO: this needs to be a private function (wait till we have the cmake story better before moving it though).
 * It should be external for the purpose of other libs we own,
 * but customers should not be able to hit it without going out of their way to do so.
 */
AWS_COMMON_API void aws_register_error_info(const struct aws_error_info_list *error_info);

#ifdef _cplusplus
}
#endif

#endif /* AWS_COMMON_ERROR_H_ */