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

#ifdef _MSC_VER
#    pragma warning(disable : 4324) /* structure was padded due to alignment specifier */
#endif

static int s_byte_swap_test_fn(struct aws_allocator *allocator, void *ctx) {
    (void)allocator;
    (void)ctx;

    uint64_t ans_x = 0x1122334455667788ULL;
    uint32_t ans_y = 0xaabbccdd;
    uint32_t ans_z = 0xaabbcc;
    uint16_t ans_w = 0xeeff;

    uint8_t x[] = {0x11, 0x22, 0x33, 0x44, 0x55, 0x66, 0x77, 0x88};
    uint8_t y[] = {0xaa, 0xbb, 0xcc, 0xdd};
    uint8_t z[] = {0x00, 0xaa, 0xbb, 0xcc}; /* Leading 0 needed avoid buffer overflows */
    uint8_t w[] = {0xee, 0xff};

    uint64_t x64;
    uint32_t y32;
    uint32_t z24;
    uint16_t w16;

    memcpy(&x64, x, sizeof(x));
    memcpy(&y32, y, sizeof(y));
    memcpy(&z24, z, sizeof(z));
    memcpy(&w16, w, sizeof(w));

    z24 >>= 8; /* Throw away the fake byte */

    ASSERT_UINT_EQUALS(aws_ntoh64(x64), ans_x);
    ASSERT_UINT_EQUALS(aws_hton64(x64), ans_x);

    ASSERT_UINT_EQUALS(aws_ntoh32(y32), ans_y);
    ASSERT_UINT_EQUALS(aws_hton32(y32), ans_y);

    ASSERT_UINT_EQUALS(aws_ntoh24(z24), ans_z);
    ASSERT_UINT_EQUALS(aws_hton24(z24), ans_z);
    /* Make sure top byte is untouched */
    ASSERT_UINT_EQUALS(aws_ntoh24(z24) & 0xFF000000, 0);
    ASSERT_UINT_EQUALS(aws_hton24(z24) & 0xFF000000, 0);

    ASSERT_UINT_EQUALS(aws_ntoh16(w16), ans_w);
    ASSERT_UINT_EQUALS(aws_hton16(w16), ans_w);

    return 0;
}
AWS_TEST_CASE(byte_swap_test, s_byte_swap_test_fn);

AWS_ALIGNED_TYPEDEF(uint8_t, aligned_storage[64], 32);

struct padding_disaster {
    aligned_storage a;
    uint8_t dumb;
    aligned_storage b;
};

static int s_alignment_test_fn(struct aws_allocator *allocator, void *ctx) {
    (void)allocator;
    (void)ctx;

    struct padding_disaster padded;

    ASSERT_UINT_EQUALS(0, ((intptr_t)&padded.a) % 32);
    ASSERT_UINT_EQUALS(0, ((intptr_t)&padded.b) % 32);

    return 0;
}
AWS_TEST_CASE(alignment_test, s_alignment_test_fn)
