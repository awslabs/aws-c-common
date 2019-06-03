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

AWS_EXTERN_C_BEGIN

AWS_COMMON_API
AWS_DECLSPEC_NORETURN
void aws_fatal_assert(const char *cond_str, const char *file, int line) AWS_ATTRIBUTE_NORETURN;

AWS_COMMON_API
void aws_debug_break(void);

/**
 * Print a backtrace from either the current stack, or (if provided) the current exception/signal
 *  call_site_data is siginfo_t* on POSIX, and LPEXCEPTION_POINTERS on Windows, and can be null
 */
AWS_COMMON_API
void aws_backtrace_print(FILE *fp, void *call_site_data);

AWS_EXTERN_C_END

#if defined(CBMC)
#    define AWS_FATAL_ASSERT(cond)                                                                                     \
        if (!(cond)) {                                                                                                 \
            abort();                                                                                                   \
        }
#else
#    if defined(_MSC_VER)
#        define AWS_FATAL_ASSERT(cond)                                                                                 \
            __pragma(warning(push)) __pragma(warning(disable : 4127)) /* conditional expression is constant */         \
                if (!(cond)) {                                                                                         \
                aws_fatal_assert(#cond, __FILE__, __LINE__);                                                           \
            }                                                                                                          \
            __pragma(warning(pop))
#    else
#        define AWS_FATAL_ASSERT(cond)                                                                                 \
            if (!(cond)) {                                                                                             \
                aws_fatal_assert(#cond, __FILE__, __LINE__);                                                           \
            }
#    endif
#endif

#if defined(CBMC)
#    include <assert.h>
#    define AWS_ASSERT(cond) assert(cond)
#elif defined(DEBUG_BUILD)
#    define AWS_ASSERT(cond) AWS_FATAL_ASSERT(cond)
#else
#    define AWS_ASSERT(cond)
#endif

#define AWS_STATIC_ASSERT0(cond, msg) typedef char AWS_CONCAT(static_assertion_, msg)[(!!(cond)) * 2 - 1]
#define AWS_STATIC_ASSERT1(cond, line) AWS_STATIC_ASSERT0(cond, AWS_CONCAT(at_line_, line))
#define AWS_STATIC_ASSERT(cond) AWS_STATIC_ASSERT1(cond, __LINE__)
