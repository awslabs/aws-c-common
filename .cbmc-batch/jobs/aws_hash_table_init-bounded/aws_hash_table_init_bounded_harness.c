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

/**
 * Assume an bounded size to enable using an accurate stub for memset.
 */
void aws_hash_table_init_bounded_harness() {
    struct aws_allocator *allocator = can_fail_allocator();
    size_t size;
    __CPROVER_assume(size <= MAX_TABLE_SIZE);
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
        struct hash_table_state *impl = map.p_impl;
        assert_all_zeroes((uint8_t *)&impl->slots[0], impl->size * sizeof(impl->slots[0]));
    }
}
