#ifndef AWS_COMMON_H_
#define AWS_COMMON_H_

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
#include <stddef.h>

#if defined(_MSC_VER )
#define AWS_THREAD_LOCAL __declspec(thread)
#else
#define AWS_THREAD_LOCAL __thread
#endif

/* Allocator structure. An instance of this will be passed around for anything needing memory allocation */
struct aws_allocator {
    void *(*mem_acquire)(struct aws_allocator *allocator, size_t size);
    void(*mem_release)(struct aws_allocator *allocator, void *ptr);
};

#ifdef __cplusplus
extern "C" {
#endif

AWS_COMMON_API struct aws_allocator *aws_default_allocator();

/*
 * Returns at least `size` of memory ready for usage or returns NULL on failure.
 */
AWS_COMMON_API void *aws_mem_acquire(struct aws_allocator *allocator, size_t size);

/*
 * Releases ptr back to whatever allocated it.
 */
AWS_COMMON_API void aws_mem_release(struct aws_allocator *allocator, void *ptr);

/*
 * Loads error strings for debugging and logging purposes.
 */
AWS_COMMON_API void aws_load_error_strings(void);

#ifdef __cplusplus
}
#endif

#define AWS_CACHE_LINE 64

#if defined(_MSC_VER )
#define AWS_ALIGN(alignment) __declspec(align(alignment))
#define AWS_TYPE_OF(a) __decltype(a)
#else
#if defined(__GNUC__) || defined(__clang__)
#define AWS_ALIGN(alignment) __attribute__ ((aligned(alignment)))
#define AWS_TYPE_OF(a) __typeof__(a)
#endif
#endif

/*
 * The next two macros don't do braced-group expressions since it breaks ISO-C rules. Instead just write the result to a variable.
 */
#define AWS_MIN(a, b, o) do { AWS_TYPE_OF (a) _a = (a); \
                         AWS_TYPE_OF (b) _b = (b); \
                         o = _a < _b ? _a : _b; } while(0);

#define AWS_MAX(a, b, o) do { AWS_TYPE_OF (a) _a = (a); \
                         AWS_TYPE_OF (b) _b = (b); \
                         o = _a > _b ? _a : _b; } while(0);

#define AWS_CACHE_ALIGN AWS_ALIGN(AWS_CACHE_LINE)

#define AWS_OP_SUCCESS 0
#define AWS_OP_ERR -1

typedef enum aws_common_error {
    AWS_ERROR_SUCCESS = 0,
    AWS_ERROR_OOM,
    AWS_ERROR_INVALID_BUFFER_SIZE,
    AWS_ERROR_INVALID_HEX_STR,
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
    AWS_ERROR_CLOCK_FAILURE,
    AWS_ERROR_LIST_EMPTY,
    AWS_ERROR_LIST_DEST_COPY_TOO_SMALL,
    AWS_ERROR_LIST_EXCEEDS_MAX_SIZE,
    AWS_ERROR_LIST_STATIC_MODE_CANT_SHRINK,
    AWS_ERROR_PRIORITY_QUEUE_FULL,
    AWS_ERROR_PRIORITY_QUEUE_EMPTY,

    AWS_ERROR_END_COMMON_RANGE = 0x03FF
} aws_common_error;

#define AWS_LIB_NAME "libaws-c-common"




#endif /* AWS_COMMON_H_ */
