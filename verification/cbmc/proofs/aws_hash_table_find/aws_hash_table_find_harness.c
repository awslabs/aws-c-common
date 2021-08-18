/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/common/hash_table.h>
#include <aws/common/private/hash_table_impl.h>
#include <proof_helpers/make_common_data_structures.h>
#include <proof_helpers/utils.h>

void aws_hash_table_find_harness() {
    struct aws_hash_table map;
    ensure_allocated_hash_table(&map, MAX_TABLE_SIZE);
    __CPROVER_assume(aws_hash_table_is_valid(&map));
    map.p_impl->equals_fn = uninterpreted_equals_assert_inputs_nonnull;
    map.p_impl->hash_fn = uninterpreted_hasher;

    size_t empty_slot_idx;
    __CPROVER_assume(aws_hash_table_has_an_empty_slot(&map, &empty_slot_idx));

    struct store_byte_from_buffer old_byte;
    save_byte_from_hash_table(&map, &old_byte);

    void *key;
    struct aws_hash_element *p_elem;

    /* Preconditions */
    __CPROVER_assume(aws_hash_table_is_valid(&map));
    __CPROVER_assume(AWS_OBJECT_PTR_IS_WRITABLE(&p_elem));

    int rval = aws_hash_table_find(&map, key, &p_elem);
    assert(rval == AWS_OP_SUCCESS);
    if (p_elem) {
        assert(AWS_OBJECT_PTR_IS_READABLE(p_elem));
        assert(p_elem->key == key || uninterpreted_equals(p_elem->key, key));
    }
    assert(aws_hash_table_is_valid(&map));
    check_hash_table_unchanged(&map, &old_byte);
}
