/*
 * Copyright 2018 Amazon.com, Inc. or its affiliates. All Rights Reserved.
 *
 * Licensed under the Apache License, Version 2.0 (the "License"). You may not use
 * this file except in compliance with the License. A copy of the License is
 * located at
 *
 *     http://aws.amazon.com/apache2.0/
 *
 * or in the "license" file accompanying this file. This file is distributed on an
 * "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or
 * implied. See the License for the specific language governing permissions and
 * limitations under the License.
 */

#include <aws/common/common.h>
#include <limits.h>
#include <proof_helpers/make_common_data_structures.h>
#include <proof_helpers/proof_allocators.h>
#include <stdint.h>
#include <stdlib.h>

bool is_bounded_byte_buf(struct aws_byte_buf *buf, size_t max_size) {
    return buf->capacity <= max_size;
}

bool is_byte_buf_expected_alloc(struct aws_byte_buf *buf) {
    return (buf->allocator == can_fail_allocator());
}

void ensure_byte_buf_has_allocated_buffer_member(struct aws_byte_buf *buf) {
    buf->allocator = can_fail_allocator();
    buf->buffer = bounded_malloc(sizeof(*(buf->buffer)) * buf->capacity);
}

bool is_bounded_byte_cursor(struct aws_byte_cursor *cursor, size_t max_size) {
    return cursor->len <= max_size;
}

void ensure_byte_cursor_has_allocated_buffer_member(struct aws_byte_cursor *cursor) {
    cursor->ptr = bounded_malloc(cursor->len);
}

bool aws_array_list_is_bounded(struct aws_array_list *list, size_t max_initial_item_allocation, size_t max_item_size) {
    bool item_size_is_bounded = list->item_size <= max_item_size;
    bool length_is_bounded = list->length <= max_initial_item_allocation;
    return item_size_is_bounded && length_is_bounded;
}

void ensure_array_list_has_allocated_data_member(struct aws_array_list *list) {
    if (list->current_size == 0) {
        __CPROVER_assume(list->data == NULL);
        list->alloc = can_fail_allocator();
    } else {
        list->data = bounded_malloc(list->current_size);
        list->alloc = nondet_bool() ? NULL : can_fail_allocator();
    }
}

struct aws_array_list *make_arbitrary_array_list(size_t initial_item_allocation, size_t item_size) {
    struct aws_array_list *list;
    /* Assume list is allocated */
    ASSUME_VALID_MEMORY(list);

    if (nondet_int()) { /* dynamic */
        struct aws_allocator *allocator;
        ASSUME_CAN_FAIL_ALLOCATOR(allocator);
        __CPROVER_assume(
            aws_array_list_init_dynamic(list, allocator, initial_item_allocation, item_size) == AWS_OP_SUCCESS);
    } else { /* static */
        size_t len;
        __CPROVER_assume(!aws_mul_size_checked(initial_item_allocation, item_size, &len));
        void *raw_array = can_fail_malloc(len);
        aws_array_list_init_static(list, raw_array, initial_item_allocation, item_size);
    }
    list->length = nondet_size_t();
    __CPROVER_assume(list->length <= initial_item_allocation);

    return list;
}

struct aws_array_list *make_nondet_array_list() {
    size_t initial_item_allocation = nondet_size_t();
    size_t item_size = nondet_size_t();
    struct aws_array_list *list;
    ASSUME_ARBITRARY_ARRAY_LIST(list, initial_item_allocation, item_size);
    return list;
}

struct aws_array_list *make_bounded_array_list(size_t max_initial_item_allocation, size_t max_item_size) {
    size_t initial_item_allocation = nondet_size_t();
    __CPROVER_assume(initial_item_allocation <= max_initial_item_allocation);
    size_t item_size = nondet_size_t();
    __CPROVER_assume(item_size <= max_item_size);
    struct aws_array_list *list;
    ASSUME_ARBITRARY_ARRAY_LIST(list, initial_item_allocation, item_size);
    return list;
}

struct aws_byte_cursor make_arbitrary_byte_cursor_nondet_len_max(size_t max) {
    size_t len;
    __CPROVER_assume(len <= max);
    struct aws_byte_cursor rval = {.len = len, .ptr = malloc(len)};
    return rval;
}

void make_arbitrary_byte_buf(struct aws_allocator *allocator, struct aws_byte_buf *buf, size_t capacity, size_t len) {
    buf->buffer = malloc(capacity); // use malloc because we will need to deallocate later
    buf->len = len;
    buf->capacity = capacity;
    buf->allocator = allocator;
}

void make_arbitrary_byte_buf_full(struct aws_allocator *allocator, struct aws_byte_buf *buf, size_t capacity) {
    make_arbitrary_byte_buf(allocator, buf, capacity, capacity);
}

void make_arbitrary_byte_buf_nondet_len_max(struct aws_allocator *allocator, struct aws_byte_buf *buf, size_t max) {
    size_t capacity = nondet_size_t();
    __CPROVER_assume(capacity <= max);
    size_t len = nondet_size_t();
    __CPROVER_assume(len <= capacity);
    make_arbitrary_byte_buf(allocator, buf, capacity, len);
}

struct aws_byte_buf *allocate_arbitrary_byte_buf_nondet_len_max(struct aws_allocator *allocator, size_t max) {
    struct aws_byte_buf *buf = malloc(sizeof(*buf));
    make_arbitrary_byte_buf_nondet_len_max(allocator, buf, max);
    return buf;
}

void make_arbitrary_byte_buf_nondet_len(struct aws_allocator *allocator, struct aws_byte_buf *buf) {
    size_t capacity = nondet_size_t();
    size_t len = nondet_size_t();
    __CPROVER_assume(len <= capacity);
    make_arbitrary_byte_buf(allocator, buf, capacity, len);
}

struct aws_string *make_arbitrary_aws_string(struct aws_allocator *allocator, size_t len) {
    //  __CPROVER_assume(len > 0);
    struct aws_string *str = malloc(sizeof(struct aws_string) + len + 1);

    /* Fields are declared const, so we need to copy them in like this */
    *(struct aws_allocator **)(&str->allocator) = allocator;
    *(size_t *)(&str->len) = len;
    *(uint8_t *)&str->bytes[len] = '\0';

    return str;
}

struct aws_string *make_arbitrary_aws_string_nondet_len(struct aws_allocator *allocator) {
    return make_arbitrary_aws_string_nondet_len_with_max(allocator, INT_MAX - 1 - sizeof(struct aws_string));
}

struct aws_string *make_arbitrary_aws_string_nondet_len_with_max(struct aws_allocator *allocator, size_t max) {
    size_t len;
    __CPROVER_assume(len < max);
    return make_arbitrary_aws_string(allocator, len);
}
