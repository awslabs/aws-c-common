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

#include <stdio.h>

void aws_fatal_assert(int cond, const char *cond_str, const char *file, int line);
void aws_debug_break(void);

/**
 * Print a backtrace from either the current stack, or (if provided) the current exception/signal
 *  call_site_data is siginfo_t* on POSIX, and LPEXCEPTION_POINTERS on Windows, and can be null 
 */
void aws_backtrace_print(FILE *fp, void *call_site_data);

#if defined(DEBUG_BUILD)
#define AWS_ASSERT(cond)
#else
#define AWS_ASSERT(cond) aws_fatal_assert((cond), #cond, __FILE__, __LINE__)
#endif
#define AWS_STATIC_ASSERT0(cond, msg) typedef char AWS_CONCAT(static_assertion_, msg)[(!!(cond)) * 2 - 1]
#define AWS_STATIC_ASSERT1(cond, line) AWS_STATIC_ASSERT0(cond, AWS_CONCAT(at_line_, line))
#define AWS_STATIC_ASSERT(cond) AWS_STATIC_ASSERT1(cond, __LINE__)
#define AWS_FATAL_ASSERT(cond)                                                                                         \
    if (!(cond)) {                                                                                                     \
        aws_fatal_assert(0, #cond, __FILE__, __LINE__);                                                                \
    }

#endif /* AWS_COMMON_ASSERT_H */
