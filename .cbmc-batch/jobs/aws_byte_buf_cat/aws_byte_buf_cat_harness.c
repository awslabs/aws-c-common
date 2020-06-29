/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/common/byte_buf.h>
#include <proof_helpers/make_common_data_structures.h>
#include <proof_helpers/proof_allocators.h>

void aws_byte_buf_cat_harness() {
    /* parameters */
    struct aws_byte_buf buffer1;
    struct aws_byte_buf buffer2;
    struct aws_byte_buf buffer3;
    struct aws_byte_buf dest;
    size_t number_of_args = 3;

    /* assumptions */
    __CPROVER_assume(aws_byte_buf_is_bounded(&buffer1, MAX_BUFFER_SIZE));
    ensure_byte_buf_has_allocated_buffer_member(&buffer1);
    __CPROVER_assume(aws_byte_buf_is_valid(&buffer1));
    __CPROVER_assume(aws_byte_buf_is_bounded(&buffer2, MAX_BUFFER_SIZE));
    ensure_byte_buf_has_allocated_buffer_member(&buffer2);
    __CPROVER_assume(aws_byte_buf_is_valid(&buffer2));
    __CPROVER_assume(aws_byte_buf_is_bounded(&buffer3, MAX_BUFFER_SIZE));
    ensure_byte_buf_has_allocated_buffer_member(&buffer3);
    __CPROVER_assume(aws_byte_buf_is_valid(&buffer3));
    ensure_byte_buf_has_allocated_buffer_member(&dest);
    __CPROVER_assume(aws_byte_buf_is_valid(&dest));

    /* save current state of the data structure */
    struct aws_byte_buf old_buffer1 = buffer1;
    struct store_byte_from_buffer old_byte_from_buffer1;
    save_byte_from_array(buffer1.buffer, buffer1.len, &old_byte_from_buffer1);
    struct aws_byte_buf old_buffer2 = buffer2;
    struct store_byte_from_buffer old_byte_from_buffer2;
    save_byte_from_array(buffer2.buffer, buffer2.len, &old_byte_from_buffer2);
    struct aws_byte_buf old_buffer3 = buffer3;
    struct store_byte_from_buffer old_byte_from_buffer3;
    save_byte_from_array(buffer3.buffer, buffer3.len, &old_byte_from_buffer3);
    struct aws_byte_buf old_dest = dest;
    struct store_byte_from_buffer old_byte_from_dest;
    save_byte_from_array(dest.buffer, dest.len, &old_byte_from_dest);

    /* operation under verification */
    if (aws_byte_buf_cat(&dest, number_of_args, &buffer1, &buffer2, &buffer3) == AWS_OP_SUCCESS) {
        assert((old_dest.capacity - old_dest.len) >= (buffer1.len + buffer2.len + buffer3.len));
    } else {
        assert((old_dest.capacity - old_dest.len) < (buffer1.len + buffer2.len + buffer3.len));
    }

    /* assertions */
    assert(aws_byte_buf_is_valid(&buffer1));
    assert(aws_byte_buf_is_valid(&buffer2));
    assert(aws_byte_buf_is_valid(&buffer3));
    assert(aws_byte_buf_is_valid(&dest));
    assert_byte_buf_equivalence(&buffer1, &old_buffer1, &old_byte_from_buffer1);
    assert_byte_buf_equivalence(&buffer2, &old_buffer2, &old_byte_from_buffer2);
    assert_byte_buf_equivalence(&buffer3, &old_buffer3, &old_byte_from_buffer3);
}
