/*
 * Copyright 2019 Amazon.com, Inc. or its affiliates. All Rights Reserved.
 *
 * Licensed under the Apache License, Version 2.0 (the "License").
 * You may not use this file except in compliance with the License.
 * A copy of the License is located at
 *
 *  http://aws.amazon.com/apache2.0
 *
 * or in the "license" file accompanying this file. This file is distributed
 * on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 * express or implied. See the License for the specific language governing
 * permissions and limitations under the License.
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
