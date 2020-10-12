/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/common/hash_table.h>
#include <aws/common/private/hash_table_impl.h>
#include <proof_helpers/make_common_data_structures.h>
#include <proof_helpers/proof_allocators.h>
#include <proof_helpers/utils.h>

void aws_hash_iter_next_harness() {
    struct aws_hash_table map;
    ensure_allocated_hash_table(&map, MAX_TABLE_SIZE);
    __CPROVER_assume(aws_hash_table_is_valid(&map));

    struct aws_hash_iter iter;
    iter.map = &map;
    __CPROVER_assume(aws_hash_iter_is_valid(&iter));
    enum aws_hash_iter_status old_status = iter.status;
    struct store_byte_from_buffer old_byte;
    save_byte_from_hash_table(&map, &old_byte);

    aws_hash_iter_next(&iter);

    assert(aws_hash_iter_is_valid(&iter));
    assert(iter.status == AWS_HASH_ITER_STATUS_DONE || iter.status == AWS_HASH_ITER_STATUS_READY_FOR_USE);
    assert(IMPLIES(old_status == AWS_HASH_ITER_STATUS_DONE, iter.status == AWS_HASH_ITER_STATUS_DONE));
    assert(aws_hash_table_is_valid(&map));
    check_hash_table_unchanged(&map, &old_byte);
}
