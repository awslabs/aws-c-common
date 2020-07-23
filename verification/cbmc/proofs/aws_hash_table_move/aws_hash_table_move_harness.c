/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/common/hash_table.h>
#include <aws/common/math.h>
#include <aws/common/private/hash_table_impl.h>
#include <proof_helpers/make_common_data_structures.h>
#include <proof_helpers/proof_allocators.h>
#include <proof_helpers/utils.h>

void aws_hash_table_move_harness() {
    struct aws_hash_table to;
    struct aws_hash_table from;

    // There are no loops in the code under test, so use the biggest possible value
    ensure_allocated_hash_table(&from, SIZE_MAX);
    __CPROVER_assume(aws_hash_table_is_valid(&from));

    struct store_byte_from_buffer stored_byte;
    save_byte_from_hash_table(&from, &stored_byte);

    aws_hash_table_move(&to, &from);

    // Ensure that the destination table is valid.
    assert(aws_hash_table_is_valid(&to));

    // Ensure that the two tables were byte for byte swapped
    check_hash_table_unchanged(&to, &stored_byte);
}
