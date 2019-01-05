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
#include <aws/common/string.h>

struct aws_string *aws_string_new_from_c_str(struct aws_allocator *allocator, const char *c_str) {
    return aws_string_new_from_array(allocator, (const uint8_t *)c_str, strlen(c_str));
}

struct aws_string *aws_string_new_from_array(struct aws_allocator *allocator, const uint8_t *bytes, size_t len) {
    struct aws_string *str = aws_mem_acquire(allocator, sizeof(struct aws_string) + len + 1);
    if (!str) {
        return NULL;
    }

    /* Fields are declared const, so we need to copy them in like this */
    *(struct aws_allocator **)(&str->allocator) = allocator;
    *(size_t *)(&str->len) = len;
    memcpy((void *)str->bytes, bytes, len);
    *(uint8_t *)&str->bytes[len] = '\0';

    return str;
}

struct aws_string *aws_string_new_from_string(struct aws_allocator *allocator, const struct aws_string *str) {
    return aws_string_new_from_array(allocator, str->bytes, str->len);
}

void aws_string_destroy(struct aws_string *str) {
    if (str && str->allocator) {
        aws_mem_release(str->allocator, str);
    }
}

void aws_string_destroy_secure(struct aws_string *str) {
    if (str) {
        aws_secure_zero((void *)aws_string_bytes(str), str->len);
        if (str->allocator) {
            aws_mem_release(str->allocator, str);
        }
    }
}

int aws_string_compare(const struct aws_string *a, const struct aws_string *b) {
    size_t len_a = a->len;
    size_t len_b = b->len;
    size_t min_len = len_a < len_b ? len_a : len_b;

    int ret = memcmp(aws_string_bytes(a), aws_string_bytes(b), min_len);
    if (ret) {
        return ret; /* overlapping characters differ */
    }
    if (len_a == len_b) {
        return 0; /* strings identical */
    }
    if (len_a > len_b) {
        return 1; /* string b is first n characters of string a */
    }
    return -1; /* string a is first n characters of string b */
}

int aws_array_list_comparator_string(const void *a, const void *b) {
    const struct aws_string *str_a = *(const struct aws_string **)a;
    const struct aws_string *str_b = *(const struct aws_string **)b;
    return aws_string_compare(str_a, str_b);
}
