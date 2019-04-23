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

bool has_an_empty_slot(struct aws_hash_table *map, size_t *rval) {
    struct hash_table_state *state = map->p_impl;
    __CPROVER_assume(state->entry_count > 0);
    size_t empty_slot_idx;
    __CPROVER_assume(empty_slot_idx < state->size);
    *rval = empty_slot_idx;
    return state->slots[empty_slot_idx].hash_code == 0;
}

void aws_hash_iter_delete_harness() {

    struct aws_hash_table map;
    ensure_allocated_hash_table(&map, MAX_TABLE_SIZE);
    __CPROVER_assume(aws_hash_table_is_valid(&map));
    size_t empty_slot_idx;
    __CPROVER_assume(has_an_empty_slot(&map, &empty_slot_idx));
    struct hash_table_state *state = map.p_impl;

    struct aws_hash_iter iter;
    iter.map = &map;
    __CPROVER_assume(iter.status == AWS_HASH_ITER_STATUS_READY_FOR_USE);
    __CPROVER_assume(aws_hash_iter_is_valid(&iter));

    aws_hash_iter_delete(&iter, false);
    assert(iter.status == AWS_HASH_ITER_STATUS_DELETE_CALLED);
    assert(aws_hash_iter_is_valid(&iter));

    assert_hash_table_state_is_valid(map.p_impl);
}
