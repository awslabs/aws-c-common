/*
 * Copyright 2019 Amazon.com, Inc. or its affiliates. All Rights Reserved.
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

bool aws_byte_buf_is_bounded(const struct aws_byte_buf *const buf, const size_t max_size) {
    return (buf->capacity <= max_size);
}

bool aws_byte_buf_has_allocator(const struct aws_byte_buf *const buf) {
    return (buf->allocator == can_fail_allocator());
}

void ensure_byte_buf_has_allocated_buffer_member(struct aws_byte_buf *const buf) {
    buf->allocator = (nondet_bool()) ? NULL : can_fail_allocator();
    buf->buffer = bounded_malloc(sizeof(*(buf->buffer)) * buf->capacity);
}

bool aws_byte_cursor_is_bounded(const struct aws_byte_cursor *const cursor, const size_t max_size) {
    return cursor->len <= max_size;
}

void ensure_byte_cursor_has_allocated_buffer_member(struct aws_byte_cursor *const cursor) {
    cursor->ptr = (nondet_bool()) ? NULL : bounded_malloc(cursor->len);
}

bool aws_array_list_is_bounded(
    const struct aws_array_list *const list,
    const size_t max_initial_item_allocation,
    const size_t max_item_size) {
    bool item_size_is_bounded = list->item_size <= max_item_size;
    bool length_is_bounded = list->length <= max_initial_item_allocation;
    return item_size_is_bounded && length_is_bounded;
}

void ensure_array_list_has_allocated_data_member(struct aws_array_list *const list) {
    if (list->current_size == 0 && list->length == 0) {
        __CPROVER_assume(list->data == NULL);
        list->alloc = can_fail_allocator();
    } else {
        list->data = bounded_malloc(list->current_size);
        list->alloc = nondet_bool() ? NULL : can_fail_allocator();
    }
}

bool aws_priority_queue_is_bounded(
    const struct aws_priority_queue *const queue,
    const size_t max_initial_item_allocation,
    const size_t max_item_size) {
    bool container_is_bounded =
        aws_array_list_is_bounded(&queue->container, max_initial_item_allocation, max_item_size);
    bool backpointers_is_bounded =
        aws_array_list_is_bounded(&queue->backpointers, max_initial_item_allocation, max_item_size);
    return container_is_bounded && backpointers_is_bounded;
}

void ensure_priority_queue_has_allocated_members(struct aws_priority_queue *const queue) {
    ensure_array_list_has_allocated_data_member(&queue->container);
    ensure_array_list_has_allocated_data_member(&queue->backpointers);
    queue->pred = nondet_compare;
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

void ensure_allocated_hash_table(struct aws_hash_table *map, size_t max_table_entries) {
    size_t num_entries;
    __CPROVER_assume(num_entries <= max_table_entries);
    __CPROVER_assume(aws_is_power_of_two(num_entries));

    size_t required_bytes;
    __CPROVER_assume(!hash_table_state_required_bytes(num_entries, &required_bytes));
    struct hash_table_state *impl = bounded_malloc(required_bytes);
    impl->size = num_entries;
    map->p_impl = impl;
}

void ensure_hash_table_has_valid_destroy_functions(struct aws_hash_table *map) {
    map->p_impl->destroy_key_fn = nondet_bool() ? NULL : hash_proof_destroy_noop;
    map->p_impl->destroy_value_fn = nondet_bool() ? NULL : hash_proof_destroy_noop;
}

const char *make_arbitrary_c_str(size_t max_size) {
    size_t cap;
    __CPROVER_assume(cap > 0 && cap <= max_size);
    const char *str = bounded_malloc(cap);
    /* Ensure that its a valid c string. Since all bytes are nondeterminstic, the actual
     * string length is 0..str_cap
     */
    __CPROVER_assume(str[cap - 1] == 0);
    return str;
}

bool aws_hash_table_has_an_empty_slot(const struct aws_hash_table *const map, size_t *rval) {
    struct hash_table_state *state = map->p_impl;
    __CPROVER_assume(state->entry_count > 0);
    size_t empty_slot_idx;
    __CPROVER_assume(empty_slot_idx < state->size);
    *rval = empty_slot_idx;
    return state->slots[empty_slot_idx].hash_code == 0;
}

/**
 * A correct implementation of the hash_destroy function should never have a memory
 * error on valid input. There is the question of whether the destroy functions themselves
 * are correctly called (i.e. only on valid input, no double free, etc.).  This will be tested in
 * future proofs.
 */
void hash_proof_destroy_noop(void *p) {}
