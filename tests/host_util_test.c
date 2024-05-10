/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/common/byte_buf.h>
#include <aws/common/host_utils.h>
#include <aws/testing/aws_test_harness.h>

AWS_TEST_CASE(host_util_is_ipv4, s_test_is_ipv4)
static int s_test_is_ipv4(struct aws_allocator *allocator, void *ctx) {
    (void)allocator;
    (void)ctx;

    ASSERT_TRUE(aws_host_utils_is_ipv4(aws_byte_cursor_from_c_str("0.0.0.0")));
    ASSERT_TRUE(aws_host_utils_is_ipv4(aws_byte_cursor_from_c_str("127.0.0.1")));
    ASSERT_TRUE(aws_host_utils_is_ipv4(aws_byte_cursor_from_c_str("255.255.255.255")));
    ASSERT_TRUE(aws_host_utils_is_ipv4(aws_byte_cursor_from_c_str("192.168.1.1")));

    ASSERT_FALSE(aws_host_utils_is_ipv4(aws_byte_cursor_from_c_str("256.0.0.1")));
    ASSERT_FALSE(aws_host_utils_is_ipv4(aws_byte_cursor_from_c_str("127.0.0")));
    ASSERT_FALSE(aws_host_utils_is_ipv4(aws_byte_cursor_from_c_str("127.0")));
    ASSERT_FALSE(aws_host_utils_is_ipv4(aws_byte_cursor_from_c_str("127")));
    ASSERT_FALSE(aws_host_utils_is_ipv4(aws_byte_cursor_from_c_str("")));

    ASSERT_FALSE(aws_host_utils_is_ipv4(aws_byte_cursor_from_c_str("foo.com")));
    ASSERT_FALSE(aws_host_utils_is_ipv4(aws_byte_cursor_from_c_str("a.b.c.d")));
    ASSERT_FALSE(aws_host_utils_is_ipv4(aws_byte_cursor_from_c_str("a127.0.0.1")));
    ASSERT_FALSE(aws_host_utils_is_ipv4(aws_byte_cursor_from_c_str("127.0.0.1a")));
    ASSERT_FALSE(aws_host_utils_is_ipv4(aws_byte_cursor_from_c_str("127.0.0.1011")));

    return AWS_OP_SUCCESS;
}

AWS_TEST_CASE(host_util_is_ipv6, s_test_is_ipv6)
static int s_test_is_ipv6(struct aws_allocator *allocator, void *ctx) {
    (void)allocator;
    (void)ctx;

    ASSERT_TRUE(aws_host_utils_is_ipv6(aws_byte_cursor_from_c_str("0:0:0000:0000:0000:0:0:0"), false));
    ASSERT_TRUE(aws_host_utils_is_ipv6(aws_byte_cursor_from_c_str("2001:0db8:0000:0000:0000:8a2e:0370:7334"), false));
    ASSERT_TRUE(aws_host_utils_is_ipv6(aws_byte_cursor_from_c_str("2001:0DB8:0000:0000:0000:8a2e:0370:7334"), false));
    ASSERT_TRUE(aws_host_utils_is_ipv6(aws_byte_cursor_from_c_str("fe80::1"), false));
    ASSERT_TRUE(aws_host_utils_is_ipv6(aws_byte_cursor_from_c_str("fe80::1%en0"), false));
    ASSERT_TRUE(aws_host_utils_is_ipv6(aws_byte_cursor_from_c_str("::1"), false));
    ASSERT_TRUE(aws_host_utils_is_ipv6(aws_byte_cursor_from_c_str("0:0:0:0:0:0:0:1"), false));
    ASSERT_TRUE(aws_host_utils_is_ipv6(aws_byte_cursor_from_c_str("fd00:ec2::23"), false));
    ASSERT_TRUE(aws_host_utils_is_ipv6(aws_byte_cursor_from_c_str("fd00:ec2:0:0:0:0:0:23"), false));
    ASSERT_TRUE(aws_host_utils_is_ipv6(aws_byte_cursor_from_c_str("2001:0db8:0000:0000:0000:8a2e:0370:7334"), true));
    ASSERT_TRUE(aws_host_utils_is_ipv6(aws_byte_cursor_from_c_str("fe80::1"), true));
    ASSERT_TRUE(aws_host_utils_is_ipv6(aws_byte_cursor_from_c_str("fe80::1%25en0"), true));
    ASSERT_TRUE(aws_host_utils_is_ipv6(aws_byte_cursor_from_c_str("2001:db8:85a3:8d3:1319:8a2e:370:7348"), true));

    ASSERT_FALSE(aws_host_utils_is_ipv6(aws_byte_cursor_from_c_str("2001:0db8:0000:0000:0000:8a2e:0370"), false));
    ASSERT_FALSE(aws_host_utils_is_ipv6(aws_byte_cursor_from_c_str("2001:0db8:0000:0000:0000:8a2e:0370:"), false));
    ASSERT_FALSE(aws_host_utils_is_ipv6(aws_byte_cursor_from_c_str("2001::"), false));
    ASSERT_FALSE(
        aws_host_utils_is_ipv6(aws_byte_cursor_from_c_str("2001:0db8:0000:0000:0000:8a2e:0370:7334:8745"), false));
    ASSERT_FALSE(
        aws_host_utils_is_ipv6(aws_byte_cursor_from_c_str(":2001:0db8:0000:0000:0000:8a2e:0370:7334:8745"), false));
    ASSERT_FALSE(
        aws_host_utils_is_ipv6(aws_byte_cursor_from_c_str("z001:0db8:0000:0000:0000:8a2e:0370:7334:8745"), false));
    ASSERT_FALSE(aws_host_utils_is_ipv6(aws_byte_cursor_from_c_str("z001::8a2e::8745"), false));
    ASSERT_FALSE(aws_host_utils_is_ipv6(aws_byte_cursor_from_c_str("::2001:0db8:0000:0000:8a2e:0370:7334"), false));

    ASSERT_FALSE(aws_host_utils_is_ipv6(aws_byte_cursor_from_c_str("fe80::1%en0"), true));
    ASSERT_FALSE(aws_host_utils_is_ipv6(aws_byte_cursor_from_c_str("fe80::1%24en0"), true));
    ASSERT_FALSE(aws_host_utils_is_ipv6(aws_byte_cursor_from_c_str("[fe80::1%25en0"), true));
    ASSERT_FALSE(aws_host_utils_is_ipv6(aws_byte_cursor_from_c_str("fe80::1%25en0]"), true));
    ASSERT_FALSE(aws_host_utils_is_ipv6(aws_byte_cursor_from_c_str("fe80::1%25"), true));

    return AWS_OP_SUCCESS;
}
