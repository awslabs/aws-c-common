/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/common/string.h>
#include <proof_helpers/make_common_data_structures.h>
#include <proof_helpers/proof_allocators.h>
#include <proof_helpers/utils.h>

void aws_string_new_from_array_harness() {
    /* parameters */
    size_t alloc_size;
    uint8_t *array = bounded_malloc(alloc_size);
    struct aws_allocator *allocator = can_fail_allocator();
    size_t reported_size;

    /* precondition */
    __CPROVER_assume(reported_size <= alloc_size);

    /* operation under verification */
    struct aws_string *str = aws_string_new_from_array(allocator, array, reported_size);

    /* assertions */
    if (str) {
        assert(str->len == reported_size);
        assert(str->bytes[str->len] == 0);
        assert_bytes_match(str->bytes, array, str->len);
        assert(aws_string_is_valid(str));
    }
}
