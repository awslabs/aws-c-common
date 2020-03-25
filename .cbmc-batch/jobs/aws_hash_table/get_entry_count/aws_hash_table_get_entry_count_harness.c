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
#include <aws/common/math.h>
#include <aws/common/private/hash_table_impl.h>
#include <proof_helpers/make_common_data_structures.h>
#include <proof_helpers/proof_allocators.h>
#include <proof_helpers/utils.h>

void aws_hash_table_get_entry_count_harness() {
    struct aws_hash_table table;
    /* There are no loops in the code under test, so use the biggest possible value */
    ensure_allocated_hash_table(&table, SIZE_MAX);
    __CPROVER_assume(aws_hash_table_is_valid(&table));
    struct hash_table_state *state = table.p_impl;

    struct store_byte_from_buffer stored_byte;
    save_byte_from_hash_table(&table, &stored_byte);
    size_t old_entry_count = state->entry_count;
    size_t rval = aws_hash_table_get_entry_count(&table);
    assert(rval == old_entry_count);
    /* Ensure that the table remains valid */
    assert(aws_hash_table_is_valid(&table));

    /* Ensure that table is unchanged */
    check_hash_table_unchanged(&table, &stored_byte);
}
