/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#pragma once

#include <aws/common/array_list.h>
#include <aws/common/byte_buf.h>
#include <aws/common/common.h>
#include <aws/common/linked_list.h>
#include <aws/common/priority_queue.h>
#include <aws/common/private/hash_table_impl.h>
#include <aws/common/ring_buffer.h>
#include <aws/common/string.h>
#include <proof_helpers/nondet.h>
#include <proof_helpers/utils.h>

#include <stdlib.h>

/* Assume valid memory for ptr, if count > 0 and count < MAX_MALLOC. */
#define ASSUME_VALID_MEMORY_COUNT(ptr, count)                                                                          \
    do {                                                                                                               \
        ptr = malloc(sizeof(*(ptr)) * (count));                                                                        \
        __CPROVER_assume(ptr != NULL);                                                                                 \
    } while (0)

#define ASSUME_VALID_MEMORY(ptr) ASSUME_VALID_MEMORY_COUNT(ptr, sizeof(*(ptr)))

#define ASSUME_DEFAULT_ALLOCATOR(allocator) allocator = aws_default_allocator()

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
 * Ensures aws_ring_buffer has proper allocated members
 */
void ensure_ring_buffer_has_allocated_members(struct aws_ring_buffer *ring_buf, const size_t size);
/*
 * Checks whether aws_byte_cursor is bounded by max_size
 */
bool aws_byte_cursor_is_bounded(const struct aws_byte_cursor *const cursor, const size_t max_size);

/*
 * Ensure a byte_buf is allocated within a ring_buf (a relational invariant)
 */
void ensure_byte_buf_has_allocated_buffer_member_in_ring_buf(
    struct aws_byte_buf *buf,
    struct aws_ring_buffer *ring_buf);

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

/**
 * Ensures that the aws_linked_list [list] is correctly allocated
 */
void ensure_linked_list_is_allocated(struct aws_linked_list *list, size_t max_length);

/*
 * Checks whether aws_priority_queue is bounded by max_initial_item_allocation and max_item_size
 */
bool aws_priority_queue_is_bounded(
    const struct aws_priority_queue *const queue,
    const size_t max_initial_item_allocation,
    const size_t max_item_size);

/**
 * Ensures members of an aws_priority_queue structure are correctly
 * allocated.
 */
void ensure_priority_queue_has_allocated_members(struct aws_priority_queue *const queue);

/*
 * Ensures aws_hash_table has a proper allocated p_impl member
 */
void ensure_allocated_hash_table(struct aws_hash_table *map, size_t max_table_entries);

/*
 * Ensures aws_hash_table has destroy function pointers that are enther null or valid
 */
void ensure_hash_table_has_valid_destroy_functions(struct aws_hash_table *map);

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

/**
 * Ensures a valid string is allocated, with as much nondet as possible
 */
struct aws_string *ensure_string_is_allocated_nondet_length(void);

/**
 * Ensures a valid string is allocated, with as much nondet as possible, but len < max
 */
struct aws_string *nondet_allocate_string_bounded_length(size_t max_size);

/**
 * Ensures a valid string is allocated, with as much nondet as possible, but fixed defined len
 */
struct aws_string *ensure_string_is_allocated(size_t size);

/**
 * Ensures a valid const string is allocated, with as much nondet as possible, len < max_size
 */
const char *ensure_c_str_is_allocated(size_t max_size);
