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

const struct aws_string *aws_string_from_c_str_new(struct aws_allocator *allocator, const char *c_str) {
    size_t len = strlen(c_str);
    struct aws_string *hdr = aws_mem_acquire(allocator, sizeof(struct aws_string) + len + 1);
    if (!hdr) {
        return NULL;
    }
    hdr->allocator = allocator;
    hdr->len = len;
    memcpy((void *)aws_string_bytes(hdr), c_str, len + 1);
    return hdr;
}

const struct aws_string *aws_string_from_array_new(struct aws_allocator *allocator, const uint8_t *bytes, size_t len) {
    struct aws_string *hdr = aws_mem_acquire(allocator, sizeof(struct aws_string) + len + 1);
    if (!hdr) {
        return NULL;
    }
    hdr->allocator = allocator;
    hdr->len = len;
    memcpy((void *)aws_string_bytes(hdr), bytes, len);
    uint8_t *extra_byte = (uint8_t *)aws_string_bytes(hdr) + len;
    *extra_byte = '\0';
    return hdr;
}

void aws_string_destroy(void *str) {
    struct aws_string *self = str;
    if (self && self->allocator) {
        aws_mem_release(self->allocator, self);
    }
}

void aws_string_secure_destroy(void *str) {
    struct aws_string *self = str;
    if (self) {
        aws_secure_zero((void *)aws_string_bytes(self), self->len);
        if (self->allocator)
            aws_mem_release(self->allocator, self);
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
