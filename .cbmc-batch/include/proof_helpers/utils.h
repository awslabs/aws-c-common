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
#include <proof_helpers/nondet.h>
#include <stddef.h>
#include <stdint.h>

struct store_byte_from_buffer {
    size_t index;
    uint8_t byte;
};

void assert_bytes_match(const uint8_t *a, const uint8_t *b, size_t len);
void assert_all_bytes_are(const uint8_t *a, const uint8_t c, size_t len);
void assert_all_zeroes(const uint8_t *a, size_t len);
void assert_byte_from_buffer_matches(const uint8_t *buffer, struct store_byte_from_buffer *b);

/**
 * Nondeterministically selects a byte from array and stores it into a
 * store_array_list_byte structure.
 */
void save_byte_from_array(uint8_t *array, size_t size, struct store_byte_from_buffer *storage);

/**
 * Asserts two aws_array_list structures are equivalent. Prior to using this function,
 * it is necessary to select a non-deterministic byte from the rhs aws_array_list structure
 * (use save_byte_from_array function), so it can properly assert all bytes match.
 */
void assert_array_list_equivalence(
    struct aws_array_list *lhs,
    struct aws_array_list *rhs,
    struct store_byte_from_buffer *rhs_byte);
