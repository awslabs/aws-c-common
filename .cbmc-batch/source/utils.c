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

#include <aws/common/private/hash_table_impl.h>
#include <proof_helpers/utils.h>

void assert_bytes_match(const uint8_t *a, const uint8_t *b, size_t len) {
    assert(!a == !b);
    if (len > 0 && a != NULL && b != NULL) {
        size_t i;
        __CPROVER_assume(i < len);
        assert(a[i] == b[i]);
    }
}

void assert_all_bytes_are(const uint8_t *a, const uint8_t c, size_t len) {
    if (len > 0 && a != NULL) {
        size_t i;
        __CPROVER_assume(i < len);
        assert(a[i] == c);
    }
}

void assert_all_zeroes(const uint8_t *a, size_t len) {
    assert_all_bytes_are(a, 0, len);
}

void assert_byte_from_buffer_matches(const uint8_t *buffer, struct store_byte_from_buffer *b) {
    if (buffer) {
        assert(*(buffer + b->index) == b->byte);
    }
}

void save_byte_from_array(const uint8_t *array, size_t size, struct store_byte_from_buffer *storage) {
    if (size > 0) {
        storage->index = nondet_size_t();
        __CPROVER_assume(storage->index < size);
        storage->byte = array[storage->index];
    }
}

void assert_array_list_equivalence(
    struct aws_array_list *lhs,
    struct aws_array_list *rhs,
    struct store_byte_from_buffer *rhs_byte) {
    assert(lhs->alloc == rhs->alloc);
    assert(lhs->current_size == rhs->current_size);
    assert(lhs->length == rhs->length);
    assert(lhs->item_size == rhs->item_size);
    if (lhs->current_size > 0) {
        assert_byte_from_buffer_matches((uint8_t *)lhs->data, rhs_byte);
    }
}

void save_byte_from_hash_table(const struct aws_hash_table *map, struct store_byte_from_buffer *storage) {
    struct hash_table_state *state = map->p_impl;
    size_t size_in_bytes;
    __CPROVER_assume(hash_table_state_required_bytes(state->size, &size_in_bytes) == AWS_OP_SUCCESS);
    save_byte_from_array((uint8_t *)state, size_in_bytes, storage);
}

void check_hash_table_unchanged(const struct aws_hash_table *map, const struct store_byte_from_buffer *storage) {
    struct hash_table_state *state = map->p_impl;
    uint8_t *byte_array = (uint8_t *)state;
    assert(byte_array[storage->index] == storage->byte);
}
