/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

/**
 * FUNCTION: abort
 *
 * We override abort to be an assert(0) so that it is caught by CBMC
 */

#include <assert.h>

void abort(void) {
    assert(0);
}
