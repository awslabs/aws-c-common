/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/common/string.h>
#include <proof_helpers/make_common_data_structures.h>
#include <proof_helpers/utils.h>

void aws_string_new_from_string_harness() {
    /* parameters */
    struct aws_string *source = ensure_string_is_allocated_nondet_length();
    __CPROVER_assume(aws_string_is_valid(source));
    struct aws_allocator *allocator = (source->allocator) ? source->allocator : aws_default_allocator();

    /* operation under verification */
    struct aws_string *str = aws_string_new_from_string(allocator, source);

    /* assertions */
    if (str) {
        assert(source->len == str->len);
        assert(str->allocator == allocator);
        assert(str->bytes[str->len] == '\0');
        assert_bytes_match(source->bytes, str->bytes, source->len);
        assert(aws_string_is_valid(str));
    }
    assert(aws_string_is_valid(source));
}
