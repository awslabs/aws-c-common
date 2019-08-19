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

#include <aws/common/string.h>
#include <proof_helpers/nondet.h>
#include <proof_helpers/proof_allocators.h>

/**
 * Override the aws_string_new_from_array to just give non-det bytes, rather than doing the memcpy.
 * Since we already check AWS_MEM_IS_READABLE(bytes, len) in the precondition, this is totally sound
 */
struct aws_string *aws_string_new_from_array(struct aws_allocator *allocator, const uint8_t *bytes, size_t len) {
    AWS_PRECONDITION(allocator);
    AWS_PRECONDITION(AWS_MEM_IS_READABLE(bytes, len));

    size_t malloc_size = sizeof(struct aws_string) + 1 + len;

    struct aws_string *str = bounded_malloc(malloc_size);

    __CPROVER_assume(str->allocator == allocator);
    __CPROVER_assume(str->len == len);
    __CPROVER_assume(str->bytes[len] == '\0');
    /* Fields are declared const, so we need to copy them in like this */
    // *(struct aws_allocator **)(&str->allocator) = allocator;
    //*(size_t *)(&str->len) = len;
    //*(uint8_t *)&str->bytes[len] = '\0';
    AWS_RETURN_WITH_POSTCONDITION(str, aws_string_is_valid(str));
}
