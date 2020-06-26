/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/common/byte_buf.h>
#include <aws/common/private/byte_buf.h>
#include <proof_helpers/make_common_data_structures.h>
#include <proof_helpers/proof_allocators.h>

void aws_nospec_mask_harness() {
    /* parameters */
    size_t index;
    size_t bound;

    /* operation under verification */
    size_t rval = aws_nospec_mask(index, bound);

    /* assertions */
    if (rval == 0) {
        assert((index >= bound) || (bound > (SIZE_MAX / 2)) || (index > (SIZE_MAX / 2)));
    } else {
        assert(rval == UINTPTR_MAX);
        assert(!((index >= bound) || (bound > (SIZE_MAX / 2)) || (index > (SIZE_MAX / 2))));
    }
}
