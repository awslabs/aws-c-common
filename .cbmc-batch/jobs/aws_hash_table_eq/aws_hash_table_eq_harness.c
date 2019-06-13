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

#include <aws/common/hash_table.h>
#include <aws/common/private/hash_table_impl.h>
#include <proof_helpers/make_common_data_structures.h>
#include <proof_helpers/proof_allocators.h>
#include <proof_helpers/utils.h>

void aws_hash_table_eq_harness() {
    struct aws_hash_table map_a;
    ensure_allocated_hash_table(&map_a, MAX_TABLE_SIZE);
    __CPROVER_assume(aws_hash_table_is_valid(&map_a));
    map_a.p_impl->equals_fn = uninterpreted_equals_assert_inputs_nonnull;
    map_a.p_impl->hash_fn = uninterpreted_hasher;
    struct store_byte_from_buffer old_byte_a;
    save_byte_from_hash_table(&map_a, &old_byte_a);

    struct aws_hash_table map_b;
    ensure_allocated_hash_table(&map_b, MAX_TABLE_SIZE);
    __CPROVER_assume(aws_hash_table_is_valid(&map_b));
    map_b.p_impl->equals_fn = uninterpreted_equals_assert_inputs_nonnull;
    map_b.p_impl->hash_fn = uninterpreted_hasher;
    struct store_byte_from_buffer old_byte_b;
    save_byte_from_hash_table(&map_b, &old_byte_b);

    /* assume the preconditions */
    __CPROVER_assume(aws_hash_table_is_valid(&map_a));
    __CPROVER_assume(aws_hash_table_is_valid(&map_b));

    bool rval = aws_hash_table_eq(&map_a, &map_b, uninterpreted_equals_assert_inputs_nonnull);

    assert(aws_hash_table_is_valid(&map_a));
    assert(aws_hash_table_is_valid(&map_b));
    check_hash_table_unchanged(&map_a, &old_byte_a);
    check_hash_table_unchanged(&map_b, &old_byte_b);
}
