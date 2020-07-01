/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

/**
 * FUNCTION: aws_array_list_swap
 *
 * We override aws_array_list_swap because mem_swap makes CBMC
 * struggle (because of the many memcpys) and because the
 * array_list_get_at in before the mem_swap are unneccessary if we
 * stub out mem_swap. Instead we add a havoc assumption on the two
 * swapped byted to ensure that no assertion on the values of the two
 * cells is made afterwards.
 */

#include <aws/common/array_list.h>
#include <proof_helpers/nondet.h>

void aws_array_list_swap(struct aws_array_list *AWS_RESTRICT list, size_t a, size_t b) {
    assert(a < list->length);
    assert(b < list->length);
    assert(aws_array_list_is_valid(list));

    if (a == b) {
        AWS_POSTCONDITION(aws_array_list_is_valid(list));
        return;
    }

    /* Havoc one byte of each item so that assertions on their value
     * fail */
    if (list->item_size > 0) {
        size_t item_sz = list->item_size;
        size_t offset_a;
        __CPROVER_assume(offset_a < item_sz);
        ((uint8_t *)list->data)[(a * item_sz) + offset_a] = nondet_uint8_t();

        size_t offset_b;
        __CPROVER_assume(offset_b < item_sz);
        ((uint8_t *)list->data)[(b * item_sz) + offset_b] = nondet_uint8_t();
    }

    return;
}
