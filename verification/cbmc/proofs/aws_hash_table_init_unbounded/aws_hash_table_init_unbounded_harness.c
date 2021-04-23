/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/common/hash_table.h>
#include <aws/common/private/hash_table_impl.h>
#include <proof_helpers/make_common_data_structures.h>
#include <proof_helpers/utils.h>

/**
 * Assume an unbounded size to get better coverage.
 * We make this performant by using a stub for memset
 */
void aws_hash_table_init_unbounded_harness() {
    struct aws_allocator *allocator = aws_default_allocator();
    size_t size;
    aws_hash_fn *hash_fn;
    __CPROVER_assume(hash_fn);
    aws_hash_callback_eq_fn *equals_fn;
    __CPROVER_assume(equals_fn);
    aws_hash_callback_destroy_fn *destroy_key_fn;
    aws_hash_callback_destroy_fn *destroy_value_fn;
    struct aws_hash_table map;
    int rval = aws_hash_table_init(&map, allocator, size, hash_fn, equals_fn, destroy_key_fn, destroy_value_fn);
    if (rval == AWS_OP_SUCCESS) {
        assert(aws_hash_table_is_valid(&map));
    }
}
