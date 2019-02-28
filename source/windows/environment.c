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

#include <aws/common/environment.h>

int aws_get_environment_value(const struct aws_string *variable_name, struct aws_string **value_out) {
    (void)variable_name;
    (void)value_out;

    return AWS_OP_ERR;
}

int aws_set_environment_value(const struct aws_string *variable_name, struct aws_string *value) {
    (void)variable_name;
    (void)value;

    return AWS_OP_ERR;
}

int aws_unset_environment_value(const struct aws_string *variable_name) {
    (void)variable_name;

    return AWS_OP_ERR;
}