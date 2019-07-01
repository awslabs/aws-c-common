#ifndef AWS_COMMON_ASSERT_H
#define AWS_COMMON_ASSERT_H

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
#include <aws/common/macros.h>
#include <stdio.h>

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

#if defined(CBMC) || __clang_analyzer__
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
#    endif /* defined(_MSC_VER) */
#endif     /* defined(CBMC) || __clang_analyzer__ */

#if defined(CBMC)
#    include <assert.h>
#    define AWS_ASSERT(cond) assert(cond)
#elif defined(DEBUG_BUILD) || __clang_analyzer__
#    define AWS_ASSERT(cond) AWS_FATAL_ASSERT(cond)
#else
#    define AWS_ASSERT(cond)
#endif /*  defined(CBMC) */

#define AWS_STATIC_ASSERT0(cond, msg) typedef char AWS_CONCAT(static_assertion_, msg)[(!!(cond)) * 2 - 1]
#define AWS_STATIC_ASSERT1(cond, line) AWS_STATIC_ASSERT0(cond, AWS_CONCAT(at_line_, line))
#define AWS_STATIC_ASSERT(cond) AWS_STATIC_ASSERT1(cond, __LINE__)

/**
 * Define function contracts.
 * When the code is being verified using CBMC these contracts are formally verified;
 * When the code is built in debug mode, they are checked as much as possible using assertions
 * When the code is built in production mode, they are not checked.
 * Violations of the function contracts are undefined behaviour.
 */
#ifdef CBMC
#    define AWS_PRECONDITION_2(cond, explanation) __CPROVER_precondition((cond), (explanation))
#    define AWS_PRECONDITION_1(cond) __CPROVER_precondition((cond), #    cond " check failed")
#    define AWS_POSTCONDITION_2(cond, explanation) __CPROVER_assert((cond), (explanation))
#    define AWS_POSTCONDITION_1(cond) __CPROVER_assert((cond), #    cond " check failed")
#    define AWS_MEM_IS_READABLE(base, len) __CPROVER_r_ok((base), (len))
#    define AWS_MEM_IS_WRITABLE(base, len) __CPROVER_w_ok((base), (len))
#else
#    define AWS_PRECONDITION_2(cond, expl) AWS_ASSERT(cond)
#    define AWS_PRECONDITION_1(cond) AWS_ASSERT(cond)
#    define AWS_POSTCONDITION_2(cond, expl) AWS_ASSERT(cond)
#    define AWS_POSTCONDITION_1(cond) AWS_ASSERT(cond)
/* the C runtime does not give a way to check these properties,
 * but we can at least check that the pointer is valid */
#    define AWS_MEM_IS_READABLE(base, len) (((len) == 0) || (base))
#    define AWS_MEM_IS_WRITABLE(base, len) (((len) == 0) || (base))
#endif /* CBMC */

// The UNUSED is used to silence the complains of GCC for zero arguments in variadic macro
#define AWS_PRECONDITION(...) GET_MACRO(__VA_ARGS__, AWS_PRECONDITION_2, AWS_PRECONDITION_1, UNUSED)(__VA_ARGS__)
#define AWS_POSTCONDITION(...) GET_MACRO(__VA_ARGS__, AWS_POSTCONDITION_2, AWS_POSTCONDITION_1, UNUSED)(__VA_ARGS__)

#define AWS_OBJECT_PTR_IS_READABLE(ptr) AWS_MEM_IS_READABLE((ptr), sizeof(*ptr))
#define AWS_OBJECT_PTR_IS_WRITABLE(ptr) AWS_MEM_IS_WRITABLE((ptr), sizeof(*ptr))

#endif /* AWS_COMMON_ASSERT_INL */
