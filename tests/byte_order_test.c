/*
 * Copyright 2010-2018 Amazon.com, Inc. or its affiliates. All Rights Reserved.
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

#include <aws/common/byte_order.h>
#include <aws/testing/aws_test_harness.h>

static int byte_swap_test_fn(struct aws_allocator *alloc, void *ctx) {
    uint64_t x = 0x1122334455667788ULL;
    uint64_t rev_x = 0x8877665544332211ULL;

    uint32_t y = 0xaabbccdd;
    uint32_t rev_y = 0xddccbbaa;

    uint16_t z = 0xeeff;
    uint16_t rev_z = 0xffee;

    // Since I know of no more reliable way to detect endianness
    // than is_big_endian(), attempts to test it are not helpful.
    // Instead, we assume it works to test the rest of the functionality.
    if (is_big_endian()) {
        ASSERT_UINT_EQUALS(ntoh64(x), x);
        ASSERT_UINT_EQUALS(hton64(x), x);

        ASSERT_UINT_EQUALS(ntoh32(y), y);
        ASSERT_UINT_EQUALS(hton32(y), y);

        ASSERT_UINT_EQUALS(ntoh16(z), z);
        ASSERT_UINT_EQUALS(ntoh16(z), z);
    } else {
        ASSERT_UINT_EQUALS(ntoh64(x), rev_x);
        ASSERT_UINT_EQUALS(hton64(x), rev_x);

        ASSERT_UINT_EQUALS(ntoh32(y), rev_y);
        ASSERT_UINT_EQUALS(hton32(y), rev_y);

        ASSERT_UINT_EQUALS(ntoh16(z), rev_z);
        ASSERT_UINT_EQUALS(ntoh16(z), rev_z);
    }

    return 0;
}
AWS_TEST_CASE(byte_swap_test, byte_swap_test_fn);
