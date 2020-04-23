#ifndef AWS_COMMON_PROCESS_H
#define AWS_COMMON_PROCESS_H
/*
 * Copyright 2010-2019 Amazon.com, Inc. or its affiliates. All Rights Reserved.
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

AWS_COMMON_API int aws_get_pid(void);

struct aws_run_command_result {
    /* return code from running the command. */
    int ret_code;

    /**
     * captured stdout message from running the command,
     * caller is responsible for releasing the memory.
     */
    struct aws_string *std_out;

    /**
     * captured stderr message from running the command,
     * caller is responsible for releasing the memory.
     * It's currently not implemented and the value will be set to NULL.
     */
    struct aws_string *std_err;
};

struct aws_run_command_options {
    /* command path and commandline options of running that command. */
    const char *command;
};

AWS_COMMON_API int aws_run_command_result_init(struct aws_allocator *allocator, struct aws_run_command_result *result);

AWS_COMMON_API void aws_run_command_result_cleanup(struct aws_run_command_result *result);

/**
 * Currently this API is implemented using popen on Posix system and
 * _popen on Windows to capture output from running a command. Note
 * that popen only captures stdout, and doesn't provide an option to
 * capture stderr. We will add more options, such as acquire stderr
 * in the future so probably will alter the underlying implementation
 * as well.
 */
AWS_COMMON_API int aws_run_command(
    struct aws_allocator *allocator,
    struct aws_run_command_options *options,
    struct aws_run_command_result *result);

AWS_EXTERN_C_END

#endif /* AWS_COMMON_PROCESS_H */
