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

#include <aws/common/string.h>

#include <stdlib.h>

int aws_get_environment_value(
	struct aws_allocator *allocator,
	const struct aws_string *variable_name,
	struct aws_string **value_out) {

#	pragma warning( push )
#   pragma warning(disable : 4996)

	const char *value = getenv((const char *)variable_name->bytes);

#	pragma warning( pop )

	if (value == NULL) {
		*value_out = NULL;
		return AWS_OP_SUCCESS;
	}

	*value_out = aws_string_new_from_c_str(allocator, value);
	if (*value_out == NULL) {
		return AWS_OP_ERR;
	}

	return AWS_OP_SUCCESS;
}

int aws_set_environment_value(const struct aws_string *variable_name, const struct aws_string *value) {
	if (_putenv_s((const char *)variable_name->bytes, (const char *)value->bytes) != 0) {
		return AWS_OP_ERR;
	}

    return AWS_OP_SUCCESS;
}

AWS_STATIC_STRING_FROM_LITERAL(s_empty_string, "");

int aws_unset_environment_value(const struct aws_string *variable_name) {
	return aws_set_environment_value(variable_name, s_empty_string);
}
