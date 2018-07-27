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

#include <aws/common/exports.h>

#include <stddef.h>
#include <string.h>

#define AWS_STATIC_ASSERT0(cond, msg) typedef char static_assertion_##msg[(!!(cond)) * 2-1]
#define AWS_STATIC_ASSERT1(cond, line) AWS_STATIC_ASSERT0(cond, static_assertion_at_line_##line)
#define AWS_STATIC_ASSERT(cond) AWS_STATIC_ASSERT1(cond, __LINE__)

#if defined(_MSC_VER )
#include <Windows.h> /* for SecureZeroMemory */
#endif

#ifndef NO_STDBOOL
#include <stdbool.h>
#else
#    ifndef __cplusplus
#        define bool _Bool
#        define true 1
#        define false 0
#    elif defined(__GNUC__) && !defined(__STRICT_ANSI__)

#        define _Bool bool
#        if  __cplusplus < 201103L
/* For C++98, define bool, false, true as a GNU extension. */
#            define bool  bool
#            define false false
#            define true  true
#        endif
#    endif
#endif

#ifndef NO_STDINT
#include <stdint.h>
#else
#    if defined(__x86_64__) || defined(_M_AMD64) || defined(__aarch64__)                \
         || defined(__ia64__) || defined(__powerpc64__)
#        define PTR_SIZE 8
#    else
#        define PTR_SIZE 4
#    endif

     typedef signed char int8_t;
     typedef short int int16_t;
     typedef int int32_t;
#    if (PTR_SIZE == 8)
        typedef long int int64_t;
#    else
        typedef long long int int64_t;
#    endif

     typedef unsigned char uint8_t;
     typedef unsigned short int uint16_t;

     typedef unsigned int uint32_t;

#    if (PTR_SIZE == 8)
         typedef unsigned long int uint64_t;
#    else
         typedef unsigned long long int uint64_t;
#    endif

#    if (PTR_SIZE == 8)
         typedef long int intptr_t;
         typedef unsigned long int uintptr_t;
#    else
         typedef int  intptr_t;
         typedef unsigned int uintptr_t;
#    endif

#    if (PTR_SIZE == 8)
#        define __INT64_C(c)  c ## L
#        define __UINT64_C(c) c ## UL
#    else
#        define __INT64_C(c)  c ## LL
#        define __UINT64_C(c) c ## ULL
#    endif

#    define INT8_MIN  (-128)
#    define INT16_MIN (-32767-1)
#    define INT32_MIN (-2147483647-1)
#    define INT64_MIN (-__INT64_C(9223372036854775807)-1)
#    define INT8_MAX  (127)
#    define INT16_MAX (32767)
#    define INT32_MAX (2147483647)
#    define INT64_MAX (__INT64_C(9223372036854775807))
#    define UINT8_MAX (255)
#    define UINT16_MAX (65535)
#    define UINT32_MAX (4294967295U)
#    define UINT64_MAX (__UINT64_C(18446744073709551615))

     AWS_STATIC_ASSERT(sizeof(uint64_t) == 8);
     AWS_STATIC_ASSERT(sizeof(uint32_t) == 4);
     AWS_STATIC_ASSERT(sizeof(uint16_t) == 2);
     AWS_STATIC_ASSERT(sizeof(uint8_t) == 1);
     AWS_STATIC_ASSERT(sizeof(int64_t) == 8);
     AWS_STATIC_ASSERT(sizeof(int32_t) == 4);
     AWS_STATIC_ASSERT(sizeof(int16_t) == 2);
     AWS_STATIC_ASSERT(sizeof(int8_t) == 1);
     AWS_STATIC_ASSERT(sizeof(uintptr_t) == sizeof(void *));
     AWS_STATIC_ASSERT(sizeof(intptr_t) == sizeof(void *));
     AWS_STATIC_ASSERT(sizeof(char) == 1);
#endif

#include <aws/common/error.h>

#if defined(_MSC_VER )
#    define AWS_THREAD_LOCAL __declspec(thread)
#else
#    define AWS_THREAD_LOCAL __thread
#endif

/* Allocator structure. An instance of this will be passed around for anything needing memory allocation */
struct aws_allocator {
    void *(*mem_acquire)(struct aws_allocator *allocator, size_t size);
    void(*mem_release)(struct aws_allocator *allocator, void *ptr);
    /* Optional method; if not supported, this pointer must be NULL */
    void *(*mem_realloc)(struct aws_allocator *allocator, void *oldptr, size_t oldsize, size_t newsize);
    void *impl;
};

/* Avoid pulling in CoreFoundation headers in a header file. */
#ifdef __MACH__
    struct __CFAllocator;
    typedef const struct __CFAllocator *CFAllocatorRef;
#endif

#ifdef __cplusplus
extern "C" {
#endif

AWS_COMMON_API struct aws_allocator *aws_default_allocator();

#ifdef __MACH__
/**
 * Wraps a CFAllocator around aws_allocator. For Mac only. Use this anytime you need a CFAllocatorRef for interacting with Apple Frameworks.
 * Unfortunately, it allocates memory so we can't make it static file scope, be sure to call aws_wrapped_cf_allocator_destroy
 * when finished.
 */
AWS_COMMON_API CFAllocatorRef aws_wrapped_cf_allocator_new(struct aws_allocator *allocator);

/**
 * Cleans up any resources alloced in aws_wrapped_cf_allocator_new.
 */
AWS_COMMON_API void aws_wrapped_cf_allocator_destroy(CFAllocatorRef allocator);
#endif

/*
 * Returns at least `size` of memory ready for usage or returns NULL on failure.
 */
AWS_COMMON_API void *aws_mem_acquire(struct aws_allocator *allocator, size_t size);

/*
 * Releases ptr back to whatever allocated it.
 */
AWS_COMMON_API void aws_mem_release(struct aws_allocator *allocator, void *ptr);

/*
 * Attempts to adjust the size of the pointed-to memory buffer from oldsize to
 * newsize. The pointer (*ptr) may be changed if the memory needs to be
 * reallocated.
 *
 * If reallocation fails, *ptr is unchanged, and this method raises an
 * AWS_ERROR_OOM error.
 */
AWS_COMMON_API int aws_mem_realloc(struct aws_allocator *allocator, void **ptr, size_t oldsize, size_t newsize);
/*
 * Maintainer note: The above function doesn't return the pointer (as with
 * standard C realloc) as this pattern becomes error-prone when OOMs occur.
 * In particular, we want to avoid losing the old pointer when an OOM condition
 * occurs, so we prefer to take the old pointer as an in/out reference argument
 * that we can leave unchanged on failure.
 */


/*
 * Loads error strings for debugging and logging purposes.
 */
AWS_COMMON_API void aws_load_error_strings(void);

#ifdef __cplusplus
}
#endif

#define AWS_CACHE_LINE 64

#if defined(_MSC_VER )
#    define AWS_ALIGN(alignment) __declspec(align(alignment))
#    define AWS_LIKELY(x) x
#    define AWS_UNLIKELY(x) x
#    define AWS_FORCE_INLINE __forceinline
#else
#    if defined(__GNUC__) || defined(__clang__)
#        define AWS_ALIGN(alignment) __attribute__ ((aligned(alignment)))
#        define AWS_TYPE_OF(a) __typeof__(a)
#        define AWS_LIKELY(x) __builtin_expect(!!(x), 1)
#        define AWS_UNLIKELY(x) __builtin_expect(!!(x), 0)
#        define AWS_FORCE_INLINE __attribute__((always_inline))
#     endif
#endif

/* If this is C++, restrict isn't supported. If this is not at least C99 on gcc and clang, it isn't supported.
 * If visual C++ building in C mode, the restrict definition is __restrict.
 * This just figures all of that out based on who's including this header file. */
#if defined (__cplusplus)
#    define AWS_RESTRICT
#else
#    if defined (_MSC_VER )
#        define AWS_RESTRICT __restrict
#    else
#        if  defined (__STDC_VERSION__) && __STDC_VERSION__ >= 199901L
#            define AWS_RESTRICT restrict
#        else
#            define AWS_RESTRICT
#        endif
#    endif
#endif

#define AWS_CACHE_ALIGN AWS_ALIGN(AWS_CACHE_LINE)

#define AWS_OP_SUCCESS 0
#define AWS_OP_ERR -1

typedef enum aws_common_error {
    AWS_ERROR_SUCCESS = 0,
    AWS_ERROR_OOM,
    AWS_ERROR_BAD_FREE,
    AWS_ERROR_MEMORY_LEAK,
    AWS_ERROR_UNKNOWN,
    AWS_ERROR_INVALID_ARGUMENT,
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
    AWS_ERROR_UNIMPLEMENTED,
    AWS_ERROR_LOG_UNINITIALIZED,
    AWS_ERROR_LOG_DOUBLE_INITIALIZE,
    AWS_ERROR_LOG_IMPROPER_CLEAN_UP,
    AWS_ERROR_LOG_THREAD_MAX_CAPACITY,
    AWS_ERROR_LOG_MAX_MESSAGE_CAPACITY,

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

#define AWS_ZERO_STRUCT(object) memset(&object, 0, sizeof(object));
#define AWS_ZERO_ARRAY(array) memset((void *)array, 0, sizeof(array));

#if defined(_MSC_VER)

#   define AWS_WARNING_PUSH __pragma(warning(push))
#   define AWS_WARNING_POP __pragma(warning(pop))
#   define AWS_WARNING_DISABLE_CONST_CONDITIONAL __pragma(warning(disable:4127)) /* Suppress warnings for const conditionals (for the below LOG macros). */

#else

#   define AWS_WARNING_PUSH
#   define AWS_WARNING_POP
#   define AWS_WARNING_DISABLE_CONST_CONDITIONAL

#endif

#define AWS_ENABLE_HW_OPTIMIZATION 1

#endif /* AWS_COMMON_H_ */
