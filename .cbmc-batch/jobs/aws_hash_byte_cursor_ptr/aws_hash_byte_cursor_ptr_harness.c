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

void aws_hash_byte_cursor_ptr_harness() {
    struct aws_byte_cursor cur;

    __CPROVER_assume(aws_byte_cursor_is_bounded(&cur, MAX_CURSOR_SIZE));
    ensure_byte_cursor_has_allocated_buffer_member(&cur);
    __CPROVER_assume(aws_byte_cursor_is_valid(&cur));

    /* This function has no pre or post conditions */
    uint64_t rval = aws_hash_byte_cursor_ptr(&cur);

    assert(aws_byte_cursor_is_valid(&cur));
}
