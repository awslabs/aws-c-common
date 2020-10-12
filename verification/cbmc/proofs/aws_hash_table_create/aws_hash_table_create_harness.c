/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/common/hash_table.h>
#include <aws/common/private/hash_table_impl.h>
#include <proof_helpers/make_common_data_structures.h>
#include <proof_helpers/proof_allocators.h>
#include <proof_helpers/utils.h>

void aws_hash_table_create_harness() {
    struct aws_hash_table map;
    ensure_allocated_hash_table(&map, MAX_TABLE_SIZE);
    __CPROVER_assume(aws_hash_table_is_valid(&map));
    map.p_impl->equals_fn = uninterpreted_equals_assert_inputs_nonnull;
    map.p_impl->hash_fn = uninterpreted_hasher;
    map.p_impl->alloc = can_fail_allocator();

    size_t empty_slot_idx;
    __CPROVER_assume(aws_hash_table_has_an_empty_slot(&map, &empty_slot_idx));
    void *key;
    struct aws_hash_element *p_elem;
    bool get_p_elem;
    bool track_was_created;
    int was_created;

    struct hash_table_state old_state = *map.p_impl;

    int rval = aws_hash_table_create(&map, key, get_p_elem ? &p_elem : NULL, track_was_created ? &was_created : NULL);
    assert(aws_hash_table_is_valid(&map));
    if (rval == AWS_OP_SUCCESS) {
        if (track_was_created) {
            assert(map.p_impl->entry_count == old_state.entry_count + was_created);
        } else {
            assert(
                map.p_impl->entry_count == old_state.entry_count ||
                map.p_impl->entry_count == old_state.entry_count + 1);
        }

        if (get_p_elem) {
            assert(uninterpreted_equals(p_elem->key, key));
        }
    } else {
        assert(map.p_impl->entry_count == old_state.entry_count);
    }
}
