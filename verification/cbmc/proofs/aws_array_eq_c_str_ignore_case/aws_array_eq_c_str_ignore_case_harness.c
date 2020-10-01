/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/common/byte_buf.h>
#include <proof_helpers/make_common_data_structures.h>
#include <proof_helpers/proof_allocators.h>

void aws_array_eq_c_str_ignore_case_harness() {
    /* assumptions */
    size_t array_len;
    __CPROVER_assume(array_len <= MAX_BUFFER_SIZE);
    void *array = can_fail_malloc(array_len);
    const char *c_str = ensure_c_str_is_allocated(MAX_BUFFER_SIZE);

    /* save current state of the parameters */
    struct store_byte_from_buffer old_byte_from_array;
    save_byte_from_array((uint8_t *)array, array_len, &old_byte_from_array);
    size_t str_len = (c_str != NULL) ? strlen(c_str) : 0;
    struct store_byte_from_buffer old_byte_from_str;
    save_byte_from_array((uint8_t *)c_str, str_len, &old_byte_from_str);

    /* pre-conditions */
    __CPROVER_assume(array || (array_len == 0));
    __CPROVER_assume(c_str);

    /* operation under verification */
    if (aws_array_eq_c_str_ignore_case(array, array_len, c_str)) {
        assert(array_len == str_len);
    }

    /* asserts both parameters remain unchanged */
    if (array_len > 0) {
        assert_byte_from_buffer_matches((uint8_t *)array, &old_byte_from_array);
    }
    if (str_len > 0) {
        assert_byte_from_buffer_matches((uint8_t *)c_str, &old_byte_from_str);
    }
}
