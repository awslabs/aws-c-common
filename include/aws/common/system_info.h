#ifndef AWS_COMMON_SYSTEM_INFO_H
#define AWS_COMMON_SYSTEM_INFO_H

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

#include <aws/common/common.h>

AWS_EXTERN_C_BEGIN

/* Returns the number of online processors available for usage. */
AWS_COMMON_API
size_t aws_system_info_processor_count(void);

/* Returns true if a debugger is currently attached to the process. */
AWS_COMMON_API
bool aws_is_debugger_present(void);

/* If a debugger is attached to the process, trip a breakpoint. */
AWS_COMMON_API
void aws_debug_break(void);

/*
 * Records a stack trace from the call site.
 * Returns the number of stack entries/stack depth captured, or 0 if the operation
 * is not supported on this platform
 */
AWS_COMMON_API
int aws_backtrace(void **frames, size_t num_frames);

/*
 * Converts stack frame pointers to symbols, if symbols are available
 * Returns an array up to stack_depth long, that needs to be free()ed.
 * Returns NULL if the platform does not support stack frame translation
 * or an error occurs
 */
char **aws_backtrace_symbols(void *const *frames, size_t stack_depth);

/*
 * Converts stack frame pointers to symbols, using all available system
 * tools to try to produce a human readable result. This call will not be
 * quick, as it shells out to addr2line or similar tools.
 * On Windows, this is the same as aws_backtrace_symbols()
 * Returns and array up to stack_depth long that needs to be free()ed.
 * Returns NULL if the platform does not support stack frame translation
 * or an error occurs
 */
char **aws_backtrace_addr2line(void *const *frames, size_t stack_depth);

AWS_EXTERN_C_END

#endif /* AWS_COMMON_SYSTEM_INFO_H */
