/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/common/hash_table.h>
#include <aws/common/private/hash_table_impl.h>
#include <proof_helpers/make_common_data_structures.h>
#include <proof_helpers/utils.h>

void aws_hash_table_remove_harness() {
    struct aws_hash_table map;
    ensure_allocated_hash_table(&map, MAX_TABLE_SIZE);
    __CPROVER_assume(aws_hash_table_is_valid(&map));
    map.p_impl->destroy_key_fn = nondet_bool() ? NULL : hash_proof_destroy_noop;
    map.p_impl->destroy_value_fn = nondet_bool() ? NULL : hash_proof_destroy_noop;
    map.p_impl->equals_fn = uninterpreted_equals_assert_inputs_nonnull;
    map.p_impl->hash_fn = uninterpreted_hasher;
    map.p_impl->alloc = aws_default_allocator();

    size_t empty_slot_idx;
    __CPROVER_assume(aws_hash_table_has_an_empty_slot(&map, &empty_slot_idx));
    void *key;
    struct aws_hash_element p_elem;
    bool get_p_elem;
    bool track_was_present;
    int was_present;

    struct hash_table_state old_state = *map.p_impl;

    /* assume the preconditions */
    __CPROVER_assume(aws_hash_table_is_valid(&map));
    __CPROVER_assume(AWS_OBJECT_PTR_IS_WRITABLE(&p_elem));
    __CPROVER_assume(AWS_OBJECT_PTR_IS_WRITABLE(&was_present));

    int rval = aws_hash_table_remove(&map, key, get_p_elem ? &p_elem : NULL, track_was_present ? &was_present : NULL);
    assert(aws_hash_table_is_valid(&map));
    if (rval == AWS_OP_SUCCESS) {
        if (track_was_present) {
            assert(map.p_impl->entry_count == old_state.entry_count - was_present);
        } else {
            assert(
                map.p_impl->entry_count == old_state.entry_count ||
                map.p_impl->entry_count == old_state.entry_count - 1);
        }

        if (get_p_elem && track_was_present && was_present == 1) {
            assert(uninterpreted_equals(p_elem.key, key));
        }
    } else {
        assert(map.p_impl->entry_count == old_state.entry_count);
    }
}
