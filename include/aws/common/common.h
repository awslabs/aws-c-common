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
#include <string.h>

#if defined(_MSC_VER )
#include <Windows.h> // for SecureZeroMemory
#endif

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
#define AWS_LIKELY(x) x
#define AWS_UNLIKELY(x) x
#define AWS_FORCE_INLINE __forceinline
#else
#if defined(__GNUC__) || defined(__clang__)
#define AWS_ALIGN(alignment) __attribute__ ((aligned(alignment)))
#define AWS_TYPE_OF(a) __typeof__(a)
#define AWS_LIKELY(x) __builtin_expect(!!(x), 1)
#define AWS_UNLIKELY(x) __builtin_expect(!!(x), 0)
#define AWS_FORCE_INLINE __attribute__((always_inline))
#endif
#endif

/* If this is C++, restrict isn't supported. If this is not at least C99 on gcc and clang, it isn't supported.
 * If visual C++ building in C mode, the restrict definition is __restrict.
 * This just figures all of that out based on who's including this header file. */
#if defined (__cplusplus)
#define AWS_RESTRICT
#else
#if defined (_MSC_VER )
#define AWS_RESTRICT __restrict
#else
#if  defined (__STDC_VERSION__) && __STDC_VERSION__ >= 199901L
#define AWS_RESTRICT restrict
#else
#define AWS_RESTRICT
#endif
#endif
#endif

#define AWS_CACHE_ALIGN AWS_ALIGN(AWS_CACHE_LINE)

#define AWS_OP_SUCCESS 0
#define AWS_OP_ERR -1

typedef enum aws_common_error {
    AWS_ERROR_SUCCESS = 0,
    AWS_ERROR_OOM,
    AWS_ERROR_UNKNOWN,
    AWS_ERROR_SHORT_BUFFER,
    AWS_ERROR_OVERFLOW_DETECTED,
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
    AWS_ERROR_TASK_SCHEDULER_NO_TASKS,
    AWS_ERROR_TASK_SCHEDULER_NO_READY_TASKS,
    AWS_ERROR_HASHTBL_ITEM_NOT_FOUND,

    AWS_ERROR_END_COMMON_RANGE = 0x03FF
} aws_common_error;

/**
 * Securely zeroes a memory buffer. This function will attempt to ensure that
 * the compiler will not optimize away this zeroing operation.
 */
static inline void aws_secure_zero(void *pBuf, size_t bufsize) {
#if defined(_MSC_VER)
    SecureZeroMemory(pBuf, bufsize);
#else
    /* We cannot use memset_s, even on a C11 compiler, because that would require
     * that __STDC_WANT_LIB_EXT1__ be defined before the _first_ inclusion of string.h.
     *
     * We'll try to work around this by using inline asm on GCC-like compilers, and
     * by exposing the buffer pointer in a volatile local pointer elsewhere.
     */
# if defined(__GNUC__) || defined(__clang__)
     memset(pBuf, 0, bufsize);
     /* This inline asm serves to convince the compiler that the buffer is (somehow) still
      * used after the zero, and therefore that the optimizer can't eliminate the memset.
      */
     __asm__ __volatile__("" /* The asm doesn't actually do anything. */
        : /* no outputs */
        /* Tell the compiler that the asm code has access to the pointer to the buffer,
         * and therefore it might be reading the (now-zeroed) buffer.
         * Without this. clang/LLVM 9.0.0 optimizes away a memset of a stack buffer.
         */
        : "r" (pBuf)
        /* Also clobber memory. While this seems like it might be unnecessary - after all,
         * it's enough that the asm might read the buffer, right? - in practice GCC 7.3.0
         * seems to optimize a zero of a stack buffer without it.
         */
        : "memory"
    );
# else // not GCC/clang
    /* We don't have access to inline asm, since we're on a non-GCC platform. Move the pointer
     * through a volatile pointer in an attempt to confuse the optimizer.
     */
    volatile void *pVolBuf = pBuf;
    memset(pVolBuf, 0, bufsize);
# endif // #else not GCC/clang
#endif  // #else not windows
}

#define AWS_LIB_NAME "libaws-c-common"

#define AWS_ENABLE_HW_OPTIMIZATION 1

#endif /* AWS_COMMON_H_ */
