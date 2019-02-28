
#ifndef AWS_COMMON_ENVIRONMENT_H
#define AWS_COMMON_ENVIRONMENT_H

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

struct aws_string;

/*
 * Simple shims to the appropriate platform calls for environment variable manipulation.
 *
 * Not thread safe to use set/unset unsynced with get.  Set/unset only used in unit tests.
 */
AWS_EXTERN_C_BEGIN

AWS_COMMON_API
int aws_get_environment_value(
    struct aws_allocator *allocator,
    const struct aws_string *variable_name,
    struct aws_string **value_out);

AWS_COMMON_API
int aws_set_environment_value(const struct aws_string *variable_name, const struct aws_string *value);

AWS_COMMON_API
int aws_unset_environment_value(const struct aws_string *variable_name);

AWS_EXTERN_C_END

#endif /* AWS_COMMON_ENVIRONMENT_H */
