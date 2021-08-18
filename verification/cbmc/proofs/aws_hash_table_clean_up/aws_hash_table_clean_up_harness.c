/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/common/hash_table.h>
#include <aws/common/private/hash_table_impl.h>
#include <proof_helpers/make_common_data_structures.h>
#include <proof_helpers/utils.h>

void aws_hash_table_clean_up_harness() {
    struct aws_hash_table map;
    ensure_allocated_hash_table(&map, MAX_TABLE_SIZE);
    __CPROVER_assume(aws_hash_table_is_valid(&map));
    ensure_hash_table_has_valid_destroy_functions(&map);
    map.p_impl->alloc = aws_default_allocator();

    struct hash_table_state *state = map.p_impl;
    size_t empty_slot_idx;
    size_t size_in_bytes = sizeof(struct hash_table_state) + sizeof(struct hash_table_entry) * state->size;

    __CPROVER_assume(aws_hash_table_has_an_empty_slot(&map, &empty_slot_idx));
    aws_hash_table_clean_up(&map);
    assert(map.p_impl == NULL);

    // Check that the bytes were zeroed.
    // This would normally raise a warning since the memory was deallocated, so use the pragma.
#pragma CPROVER check push
#pragma CPROVER check disable "pointer"
#pragma CPROVER check disable "pointer-overflow"
    size_t i;
    size_t len = state->size * sizeof(state->slots[0]);
    __CPROVER_assume(i < len);
    uint8_t *bytes = (uint8_t *)&state->slots[0];
    assert(bytes[i] == 0);
#pragma CPROVER check pop
}
