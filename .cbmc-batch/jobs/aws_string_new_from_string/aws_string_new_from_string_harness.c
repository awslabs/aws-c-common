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

void aws_string_new_from_string_harness() {
    /* parameters */
    struct aws_string *source = make_arbitrary_aws_string_nondet_len();
    struct aws_allocator *allocator = nondet_bool() ? (nondet_bool() ? can_fail_allocator() : source->allocator) : NULL;

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
