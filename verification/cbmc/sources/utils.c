/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/common/private/hash_table_impl.h>
#include <proof_helpers/utils.h>

void assert_bytes_match(const uint8_t *const a, const uint8_t *const b, const size_t len) {
    assert(len == 0 || !a == !b);
    if (len > 0 && a != NULL && b != NULL) {
        size_t i;
        __CPROVER_assume(i < len && len < MAX_MALLOC); /* prevent spurious pointer overflows */
        assert(a[i] == b[i]);
    }
}

void assert_all_bytes_are(const uint8_t *const a, const uint8_t c, const size_t len) {
    if (len > 0 && a != NULL) {
        size_t i;
        __CPROVER_assume(i < len);
        assert(a[i] == c);
    }
}

void assert_all_zeroes(const uint8_t *const a, const size_t len) {
    assert_all_bytes_are(a, 0, len);
}

void assert_byte_from_buffer_matches(const uint8_t *const buffer, const struct store_byte_from_buffer *const b) {
    if (buffer && b) {
        assert(*(buffer + b->index) == b->byte);
    }
}

void save_byte_from_array(const uint8_t *const array, const size_t size, struct store_byte_from_buffer *const storage) {
    if (size > 0 && array && storage) {
        storage->index = nondet_size_t();
        __CPROVER_assume(storage->index < size);
        storage->byte = array[storage->index];
    }
}

void assert_array_list_equivalence(
    const struct aws_array_list *const lhs,
    const struct aws_array_list *const rhs,
    const struct store_byte_from_buffer *const rhs_byte) {
    /* In order to be equivalent, either both are NULL or both are non-NULL */
    if (lhs == rhs) {
        return;
    } else {
        assert(lhs && rhs); /* if only one is null, they differ */
    }
    assert(lhs->alloc == rhs->alloc);
    assert(lhs->current_size == rhs->current_size);
    assert(lhs->length == rhs->length);
    assert(lhs->item_size == rhs->item_size);
    if (lhs->current_size > 0) {
        assert_byte_from_buffer_matches((uint8_t *)lhs->data, rhs_byte);
    }
}

void assert_byte_buf_equivalence(
    const struct aws_byte_buf *const lhs,
    const struct aws_byte_buf *const rhs,
    const struct store_byte_from_buffer *const rhs_byte) {
    /* In order to be equivalent, either both are NULL or both are non-NULL */
    if (lhs == rhs) {
        return;
    } else {
        assert(lhs && rhs); /* if only one is null, they differ */
    }
    assert(lhs->len == rhs->len);
    assert(lhs->capacity == rhs->capacity);
    assert(lhs->allocator == rhs->allocator);
    if (lhs->len > 0) {
        assert_byte_from_buffer_matches(lhs->buffer, rhs_byte);
    }
}

void assert_byte_cursor_equivalence(
    const struct aws_byte_cursor *const lhs,
    const struct aws_byte_cursor *const rhs,
    const struct store_byte_from_buffer *const rhs_byte) {
    assert(!lhs == !rhs);
    if (lhs && rhs) {
        assert(lhs->len == rhs->len);
        if (lhs->len > 0) {
            assert_byte_from_buffer_matches(lhs->ptr, rhs_byte);
        }
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

int nondet_compare(const void *const a, const void *const b) {
    assert(a != NULL);
    assert(b != NULL);
    return nondet_int();
}

int __CPROVER_uninterpreted_compare(const void *const a, const void *const b);
int uninterpreted_compare(const void *const a, const void *const b) {
    assert(a != NULL);
    assert(b != NULL);
    int rval = __CPROVER_uninterpreted_compare(a, b);
    /* Compare is reflexive */
    __CPROVER_assume(IMPLIES(a == b, rval == 0));
    /* Compare is anti-symmetric*/
    __CPROVER_assume(__CPROVER_uninterpreted_compare(b, a) == -rval);
    /* If two things are equal, their hashes are also equal */
    if (rval == 0) {
        __CPROVER_assume(__CPROVER_uninterpreted_hasher(a) == __CPROVER_uninterpreted_hasher(b));
    }
    return rval;
}

bool nondet_equals(const void *const a, const void *const b) {
    assert(a != NULL);
    assert(b != NULL);
    return nondet_bool();
}

bool __CPROVER_uninterpreted_equals(const void *const a, const void *const b);
uint64_t __CPROVER_uninterpreted_hasher(const void *const a);
/**
 * Add assumptions that equality is reflexive and symmetric. Don't bother with
 * transitivity because it doesn't cause any spurious proof failures on hash-table
 */
bool uninterpreted_equals(const void *const a, const void *const b) {
    bool rval = __CPROVER_uninterpreted_equals(a, b);
    /* Equals is reflexive */
    __CPROVER_assume(IMPLIES(a == b, rval));
    /* Equals is symmetric */
    __CPROVER_assume(__CPROVER_uninterpreted_equals(b, a) == rval);
    /* If two things are equal, their hashes are also equal */
    if (rval) {
        __CPROVER_assume(__CPROVER_uninterpreted_hasher(a) == __CPROVER_uninterpreted_hasher(b));
    }
    return rval;
}

bool uninterpreted_equals_assert_inputs_nonnull(const void *const a, const void *const b) {
    assert(a != NULL);
    assert(b != NULL);
    return uninterpreted_equals(a, b);
}

uint64_t nondet_hasher(const void *a) {
    assert(a != NULL);
    return nondet_uint64_t();
}

/**
 * Standard stub function to hash one item.
 */
uint64_t uninterpreted_hasher(const void *a) {
    assert(a != NULL);
    return __CPROVER_uninterpreted_hasher(a);
}

bool __CPROVER_uninterpreted_predicate_uint8_t(uint8_t);
bool uninterpreted_predicate_fn(uint8_t value) {
    return __CPROVER_uninterpreted_predicate_uint8_t(value);
}
