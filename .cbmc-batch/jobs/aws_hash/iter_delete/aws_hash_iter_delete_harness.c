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

void aws_hash_iter_delete_harness() {

    struct aws_hash_table map;
    ensure_allocated_hash_table(&map, MAX_TABLE_SIZE);
    __CPROVER_assume(aws_hash_table_is_valid(&map));
    __CPROVER_assume(map.p_impl->destroy_key_fn == hash_proof_destroy_noop || !map.p_impl->destroy_key_fn);
    __CPROVER_assume(map.p_impl->destroy_value_fn == hash_proof_destroy_noop || !map.p_impl->destroy_value_fn);
    size_t empty_slot_idx;
    __CPROVER_assume(aws_hash_table_has_an_empty_slot(&map, &empty_slot_idx));
    struct hash_table_state *state = map.p_impl;

    struct aws_hash_iter iter;
    iter.map = &map;
    __CPROVER_assume(iter.status == AWS_HASH_ITER_STATUS_READY_FOR_USE);
    __CPROVER_assume(aws_hash_iter_is_valid(&iter));

    aws_hash_iter_delete(&iter, nondet_bool());
    assert(iter.status == AWS_HASH_ITER_STATUS_DELETE_CALLED);
    assert(aws_hash_iter_is_valid(&iter));
}
