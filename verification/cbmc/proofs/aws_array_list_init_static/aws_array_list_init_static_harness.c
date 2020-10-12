/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/common/array_list.h>
#include <proof_helpers/make_common_data_structures.h>

/**
 * Runtime: 7s
 */
void aws_array_list_init_static_harness() {
    /* data structure */
    struct aws_array_list list; /* Precondition: list is non-null */

    /* parameters */
    size_t item_size;
    size_t initial_item_allocation;
    size_t len;

    /* assumptions */
    __CPROVER_assume(initial_item_allocation > 0 && initial_item_allocation <= MAX_INITIAL_ITEM_ALLOCATION);
    __CPROVER_assume(item_size > 0 && item_size <= MAX_ITEM_SIZE);
    __CPROVER_assume(!aws_mul_size_checked(initial_item_allocation, item_size, &len));

    /* perform operation under verification */
    uint8_t *raw_array = bounded_malloc(len);
    __CPROVER_assume(raw_array != NULL);
    struct store_byte_from_buffer old_byte;
    save_byte_from_array(raw_array, len, &old_byte);

    aws_array_list_init_static(&list, raw_array, initial_item_allocation, item_size);

    /* assertions */
    assert(aws_array_list_is_valid(&list));
    assert(list.alloc == NULL);
    assert(list.item_size == item_size);
    assert(list.length == 0);
    assert(list.current_size == initial_item_allocation * item_size);
    assert_bytes_match((uint8_t *)list.data, raw_array, len);

    assert_byte_from_buffer_matches(raw_array, &old_byte);
}
