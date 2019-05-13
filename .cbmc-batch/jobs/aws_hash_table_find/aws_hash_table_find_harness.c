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

uint64_t aws_hash_proof_hasher(const void *a) {
    assert(a);
    return nondet_uint64_t();
}

void aws_hash_table_find_harness() {

    struct aws_hash_table map;
    ensure_allocated_hash_table(&map, MAX_TABLE_SIZE);
    __CPROVER_assume(aws_hash_table_is_valid(&map));
    map.p_impl->equals_fn = nondet_compare;
    map.p_impl->hash_fn = aws_hash_proof_hasher;

    size_t empty_slot_idx;
    __CPROVER_assume(aws_hash_table_has_an_empty_slot(&map, &empty_slot_idx));

    struct store_byte_from_buffer old_byte;
    save_byte_from_hash_table(&map, &old_byte);

    void *key;
    struct aws_hash_element *p_elem;
    int rval = aws_hash_table_find(&map, key, nondet_bool() ? &p_elem : NULL);
    assert(rval == AWS_OP_SUCCESS);
    if (p_elem) {
        assert(AWS_OBJECT_PTR_IS_READABLE(p_elem));
    }
    assert(aws_hash_table_is_valid(&map));
    check_hash_table_unchanged(&map, &old_byte);
}
