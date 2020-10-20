/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/common/string.h>
#include <proof_helpers/nondet.h>
#include <proof_helpers/proof_allocators.h>

/**
 * Override the aws_string_new_from_array to just give non-det bytes, rather than doing the memcpy.
 * Since we already check AWS_MEM_IS_READABLE(bytes, len) in the precondition, this is sound - it overapproximates
 * the behaviour of the real function, and has all the same memory safety checks.
 */
struct aws_string *aws_string_new_from_array(struct aws_allocator *allocator, const uint8_t *bytes, size_t len) {
    AWS_PRECONDITION(allocator);
    AWS_PRECONDITION(AWS_MEM_IS_READABLE(bytes, len));

    size_t malloc_size = sizeof(struct aws_string) + 1 + len;

    struct aws_string *str = bounded_malloc(malloc_size);

    if (str == NULL) {
        return NULL;
    }

    __CPROVER_assume(str->allocator == allocator);
    __CPROVER_assume(str->len == len);
    __CPROVER_assume(str->bytes[len] == '\0');
    AWS_RETURN_WITH_POSTCONDITION(str, aws_string_is_valid(str));
}
