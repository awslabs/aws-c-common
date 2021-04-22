/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/common/hash_table.h>
#include <aws/common/private/hash_table_impl.h>
#include <proof_helpers/make_common_data_structures.h>
#include <proof_helpers/utils.h>

int hash_table_foreach_proof_callback(void *context, struct aws_hash_element *pElement) {
    AWS_PRECONDITION(AWS_OBJECT_PTR_IS_WRITABLE(pElement), "Input pointer [pElement] must be writable.");
    return nondet_int();
}

void aws_hash_table_foreach_harness() {
    struct aws_hash_table map;
    ensure_allocated_hash_table(&map, MAX_TABLE_SIZE);
    __CPROVER_assume(aws_hash_table_is_valid(&map));
    map.p_impl->equals_fn = uninterpreted_equals_assert_inputs_nonnull;
    map.p_impl->hash_fn = uninterpreted_hasher;

    void *context;
    aws_hash_table_foreach(&map, hash_table_foreach_proof_callback, context);
    /* No obvious postconditions, other than that the map remains valid. But the iterator could have modified the table
     */
    assert(aws_hash_table_is_valid(&map));
}
