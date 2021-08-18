/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/common/string.h>

/**
 * Allocation/Deallocation using the standard aws-c-common allocators requires
 * calls through function pointers.  Until we get better function pointer support in
 * CBMC, this is expensive.  Instead, since we know we're using "malloc" to do allocation
 * in CBMC proofs, we can just directly use "free" here, saving the function pointer derefences.
 * Otherwise the same as the real function.
 */
void aws_string_destroy(struct aws_string *str) {
    AWS_PRECONDITION(!str || aws_string_is_valid(str));
    /* If the string has no allocator, its a static string and can't be freed */
    if (str && str->allocator) {
        free(str);
    }
}
