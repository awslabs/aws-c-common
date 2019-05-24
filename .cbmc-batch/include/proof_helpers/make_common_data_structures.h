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

#pragma once

#include <aws/common/array_list.h>
#include <aws/common/byte_buf.h>
#include <aws/common/common.h>
#include <aws/common/priority_queue.h>
#include <aws/common/private/hash_table_impl.h>
#include <aws/common/string.h>
#include <proof_helpers/nondet.h>
#include <proof_helpers/proof_allocators.h>
#include <proof_helpers/utils.h>

#include <stdlib.h>

#define ASSUME_VALID_MEMORY(ptr) ptr = bounded_malloc(sizeof(*(ptr)))
#define ASSUME_VALID_MEMORY_COUNT(ptr, count) ptr = bounded_malloc(sizeof(*(ptr)) * (count))
#define ASSUME_DEFAULT_ALLOCATOR(allocator) allocator = aws_default_allocator()
#define ASSUME_CAN_FAIL_ALLOCATOR(allocator) allocator = can_fail_allocator()

/*
 * Checks whether aws_byte_buf is bounded by max_size
 */
bool aws_byte_buf_is_bounded(const struct aws_byte_buf *const buf, const size_t max_size);

/*
 * Checks whether aws_byte_buf has the correct allocator
 */
bool aws_byte_buf_has_allocator(const struct aws_byte_buf *const buf);

/*
 * Ensures aws_byte_buf has a proper allocated buffer member
 */
void ensure_byte_buf_has_allocated_buffer_member(struct aws_byte_buf *const buf);

/*
 * Checks whether aws_byte_cursor is bounded by max_size
 */
bool aws_byte_cursor_is_bounded(const struct aws_byte_cursor *const cursor, const size_t max_size);

/*
 * Ensures aws_byte_cursor has a proper allocated buffer member
 */
void ensure_byte_cursor_has_allocated_buffer_member(struct aws_byte_cursor *const cursor);

/*
 * Checks whether aws_array_list is bounded by max_initial_item_allocation and max_item_size
 */
bool aws_array_list_is_bounded(
    const struct aws_array_list *const list,
    const size_t max_initial_item_allocation,
    const size_t max_item_size);

/**
 * Ensures the data member of an aws_array_list structure is correctly allocated
 */
void ensure_array_list_has_allocated_data_member(struct aws_array_list *const list);

/*
 * Checks whether aws_priority_queue is bounded by max_initial_item_allocation and max_item_size
 */
bool aws_priority_queue_is_bounded(
    const struct aws_priority_queue *const queue,
    const size_t max_initial_item_allocation,
    const size_t max_item_size);

/**
 * Ensures members of an aws_priority_queue structure are correctly allocated
 */
void ensure_priority_queue_has_allocated_members(struct aws_priority_queue *const queue);

/**
 * Makes a byte_buf, with as much nondet as possible, len < max, valid backing storage
 */
struct aws_byte_cursor make_arbitrary_byte_cursor_nondet_len_max(size_t max);

/**
 * Makes a byte_buf, with as much nondet as possible, defined len and capacity
 */
void make_arbitrary_byte_buf(struct aws_allocator *allocator, struct aws_byte_buf *buf, size_t capacity, size_t len);

/**
 * Makes a byte_buf, with as much nondet as possible, len = capacity
 */
void make_arbitrary_byte_buf_full(struct aws_allocator *allocator, struct aws_byte_buf *buf, size_t capacity);

/**
 * Makes a valid header, with as much nondet as possible, nondet len
 */
void make_arbitrary_byte_buf_nondet_len(struct aws_allocator *allocator, struct aws_byte_buf *buf);

/**
 * Makes a valid header, with as much nondet as possible, nondet len <= max
 */
void make_arbitrary_byte_buf_nondet_len_max(struct aws_allocator *allocator, struct aws_byte_buf *buf, size_t max);
struct aws_byte_buf *allocate_arbitrary_byte_buf_nondet_len_max(struct aws_allocator *allocator, size_t max);

/**
 * Makes a valid string, with as much nondet as possible, defined length
 */
struct aws_string *make_arbitrary_aws_string(struct aws_allocator *allocator, size_t size);

/**
 * Makes a valid string, with as much nondet as possible
 */
struct aws_string *make_arbitrary_aws_string_nondet_len(struct aws_allocator *allocator);

/**
 * Makes a valid string, with as much nondet as possible, len < max
 */
struct aws_string *make_arbitrary_aws_string_nondet_len_with_max(struct aws_allocator *allocator, size_t max);

/*
 * Ensures aws_hash_table has a proper allocated p_impl member
 */
void ensure_allocated_hash_table(struct aws_hash_table *map, size_t max_table_entries);

/*
 * Ensures aws_hash_table has destroy function pointers that are enther null or valid
 */
void ensure_hash_table_has_valid_destroy_functions(struct aws_hash_table *map);

/**
 * Makes a valid c string, with as much nondet as possible, len < max_size
 */
const char *make_arbitrary_c_str(size_t max_size);

/**
 * A correct hash table has max_load < size.  This means that there is always one slot empty.
 * These functions are useful for assuming that there is some (nondet) slot which is empty
 * which is necessary to prove termination for hash-table deletion code.  Should only be used inside
 * an assume because of the way it does nondet.
 */
bool aws_hash_table_has_an_empty_slot(const struct aws_hash_table *const map, size_t *const rval);
bool hash_table_state_has_an_empty_slot(const struct hash_table_state *const state, size_t *const rval);

/**
 * A correct implementation of the hash_destroy function should never have a memory
 * error on valid input. There is the question of whether the destroy functions themselves
 * are correctly called (i.e. only on valid input, no double free, etc.).  Testing this would
 * require a stronger function here.
 */
void hash_proof_destroy_noop(void *p);
