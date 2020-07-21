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

void aws_hash_table_swap_harness() {
    struct aws_hash_table a;
    struct aws_hash_table b;
    bool inita;
    bool initb;
    struct store_byte_from_buffer stored_byte_a;
    struct store_byte_from_buffer stored_byte_b;

    /* There are no loops in the code under test, so use the biggest possible value */
    if (inita) {
        ensure_allocated_hash_table(&a, SIZE_MAX);
        __CPROVER_assume(aws_hash_table_is_valid(&a));
        save_byte_from_hash_table(&a, &stored_byte_a);
    }

    if (initb) {
        ensure_allocated_hash_table(&b, SIZE_MAX);
        __CPROVER_assume(aws_hash_table_is_valid(&b));
        save_byte_from_hash_table(&b, &stored_byte_b);
    }
    aws_hash_table_swap(&a, &b);

    if (inita) {
        assert(aws_hash_table_is_valid(&b));
        check_hash_table_unchanged(&b, &stored_byte_a);
    }
    if (initb) {
        assert(aws_hash_table_is_valid(&a));
        check_hash_table_unchanged(&a, &stored_byte_b);
    }
}
