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

#pragma once

#include <aws/common/array_list.h>
#include <aws/common/byte_buf.h>
#include <aws/common/common.h>
#include <aws/common/string.h>
#include <proof_helpers/nondet.h>
#include <proof_helpers/proof_allocators.h>

#include <stdlib.h>

#define MAX_STR_LEN 2
#define MAX_BUF_LEN 2

#define ASSUME_VALID_MEMORY(ptr) ptr = malloc(sizeof(*(ptr)))
#define ASSUME_VALID_MEMORY_COUNT(ptr, count) ptr = malloc(sizeof(*(ptr)) * (count))
#define ASSUME_DEFAULT_ALLOCATOR(allocator) allocator = aws_default_allocator()
#define ASSUME_CAN_FAIL_ALLOCATOR(allocator) allocator = can_fail_allocator()
#define ASSUME_ARBITRARY_ARRAY_LIST(list, initial_item_allocation, item_size)                                          \
    list = make_arbitrary_array_list((initial_item_allocation), (item_size))
#define ASSUME_NONDET_ARRAY_LIST(list) list = make_nondet_array_list()
#define ASSUME_BOUNDED_ARRAY_LIST(list, max_initial_item_allocation, max_item_size)                                    \
    list = make_bounded_array_list((max_initial_item_allocation), (max_item_size))

/**
 * Makes an array list, with as much nondet as possible, defined initial_item_allocation and defined item_size
 */
struct aws_array_list *make_arbitrary_array_list(size_t initial_item_allocation, size_t item_size);

/**
 * Makes an array list, with as much nondet as possible
 */
struct aws_array_list *make_nondet_array_list();

/**
 * Makes an array list, with as much nondet as possible, initial_item_allocation < max_initial_item_allocation
 * item_size < max_item_size
 */
struct aws_array_list *make_bounded_array_list(size_t max_initial_item_allocation, size_t max_item_size);

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
