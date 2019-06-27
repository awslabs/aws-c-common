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
#include <proof_helpers/make_common_data_structures.h>
#include <proof_helpers/proof_allocators.h>
#include <proof_helpers/utils.h>

void aws_string_new_from_array_harness() {
    /* parameters */
    size_t alloc_size;
    uint8_t *array = bounded_malloc(alloc_size);
    struct aws_allocator *allocator = nondet_bool() ? can_fail_allocator() : NULL;
    size_t reported_size;
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
