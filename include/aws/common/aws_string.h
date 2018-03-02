#ifndef AWS_STRING_H
#define AWS_STRING_H
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
#include <string.h>

struct aws_byte_buf {
    const uint8_t *buffer;
    size_t len;
};

static inline struct aws_byte_buf aws_byte_buf_from_literal(const char *literal) {
    return {.buffer = (const uint8_t *)literal, .len = strlen(literal)};
}

static inline struct aws_byte_buf aws_byte_buf_from_c_str(const char *c_str, size_t len) {
    return {.buffer = (const uint8_t *)c_str, .len = len};
}

static inline struct aws_byte_buf aws_byte_buf_from_array(const char c_str[], size_t len) {
    return {.buffer = (const uint8_t *)&c_str[0], .len = len};
}


#endif /* AWS_STRING_H */