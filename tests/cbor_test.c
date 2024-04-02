/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/common/cbor.h>

#include <aws/testing/aws_test_harness.h>

AWS_TEST_CASE(test_cbor, s_test_cbor_fn)
static int s_test_cbor_fn(struct aws_allocator *allocator, void *ctx) {
    (void)allocator;
    (void)ctx;

    return SUCCESS;
}
