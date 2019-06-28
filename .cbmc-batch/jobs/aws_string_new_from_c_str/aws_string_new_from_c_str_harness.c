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

void aws_string_new_from_c_str_harness() {
    /* parameters */
    const char *c_str = ensure_c_str_is_allocated(MAX_STRING_LEN);
    struct aws_allocator *allocator = can_fail_allocator();

    /* operation under verification */
    struct aws_string *str = aws_string_new_from_c_str(allocator, c_str);

    /* assertions */
    if (str) {
        assert(str->len <= MAX_STRING_LEN);
        assert(str->bytes[str->len] == 0);
        assert_bytes_match(str->bytes, c_str, str->len);
        assert(aws_string_is_valid(str));
    }
    assert(aws_c_string_is_valid(c_str));
}
