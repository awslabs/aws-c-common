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

#include <aws/common/common.h>
#include <aws/testing/aws_test_harness.h>

AWS_TEST_CASE(test_secure_zero, s_test_secure_zero_fn)
static int s_test_secure_zero_fn(struct aws_allocator *allocator, void *ctx) {
    /* We can't actually test the secure part of the zero operation - anything
     * we do to observe the buffer will teach the compiler that it needs to
     * actually zero the buffer (or provide a convincing-enough simulation of
     * the same). So we'll just test that it behaves like memset.
     */

    char buf[16];

    for (int i = 0; i < sizeof(buf); i++) {
        volatile char *ptr = buf;
        ptr += i;

        *ptr = 0xDD;
    }

    aws_secure_zero(buf, sizeof(buf) / 2);

    for (int i = 0; i < sizeof(buf); i++) {
        if (i < sizeof(buf) / 2) {
            ASSERT_INT_EQUALS(0, buf[i]);
        } else {
            ASSERT_INT_EQUALS((unsigned char)0xDD, (unsigned char)buf[i]);
        }
    }

    return SUCCESS;
}
