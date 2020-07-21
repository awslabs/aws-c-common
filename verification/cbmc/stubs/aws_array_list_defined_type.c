/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/common/array_list.h>

/**
 * The array list implementation has a void* data field.  This causes problems for CBMC, because it ends up needing to
 * byte-extract everything from the data array, even if the array is only ever used for a single type.  This
 * dramatically slows down proofs (in one case, timing out after 90 minutes).  If we know what the correct type is, we
 * can do type-safe operations, and things are dramatically faster (2 minutes instead of timeout, on the proof mentioned
 * above).
 */

#include ARRAY_LIST_TYPE_HEADER

int aws_array_list_get_at_ptr(const struct aws_array_list *AWS_RESTRICT list, void **val, size_t index) {
    AWS_PRECONDITION(aws_array_list_is_valid(list));
    AWS_PRECONDITION(val != NULL);
    if (list->length > index) {
        ARRAY_LIST_TYPE *data = (ARRAY_LIST_TYPE *)(list->data);
        *val = &(data[index]);
        AWS_POSTCONDITION(aws_array_list_is_valid(list));
        return AWS_OP_SUCCESS;
    }
    AWS_POSTCONDITION(aws_array_list_is_valid(list));
    return aws_raise_error(AWS_ERROR_INVALID_INDEX);
}
