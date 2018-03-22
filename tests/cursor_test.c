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

#include <aws/common/byte_buf.h>
#include <aws/testing/aws_test_harness.h>

#define SSIZE_MAX (SIZE_MAX >> 1)

static int nospec_index_test_fn(struct aws_allocator *alloc, void *ctx) {
    ASSERT_UINT_EQUALS(0, aws_nospec_index(0, 1));
    ASSERT_UINT_EQUALS(0, aws_nospec_index(0, 0));
    ASSERT_UINT_EQUALS(0, aws_nospec_index(0, SSIZE_MAX));
    ASSERT_UINT_EQUALS(0, aws_nospec_index(0, SIZE_MAX));

    ASSERT_UINT_EQUALS(0, aws_nospec_index(1, 1));
    ASSERT_UINT_EQUALS(1, aws_nospec_index(1, 2));
    ASSERT_UINT_EQUALS(1, aws_nospec_index(1, 4));
    ASSERT_UINT_EQUALS(1, aws_nospec_index(1, SSIZE_MAX));
    ASSERT_UINT_EQUALS(0, aws_nospec_index(1, SIZE_MAX));
    ASSERT_UINT_EQUALS(0, aws_nospec_index(1, 0));

    ASSERT_UINT_EQUALS(0, aws_nospec_index(4, 3));
    ASSERT_UINT_EQUALS(0, aws_nospec_index(4, 4));
    ASSERT_UINT_EQUALS(4, aws_nospec_index(4, 5));

    ASSERT_UINT_EQUALS(SSIZE_MAX - 1, aws_nospec_index(SSIZE_MAX - 1, SSIZE_MAX));
    ASSERT_UINT_EQUALS(0, aws_nospec_index(SSIZE_MAX + 1, SSIZE_MAX));
    ASSERT_UINT_EQUALS(0, aws_nospec_index(SSIZE_MAX, SSIZE_MAX + 1));


    return 0;
}
AWS_TEST_CASE(nospec_index_test, nospec_index_test_fn)


#define ASSERT_NOADVANCE(advlen, cursorlen) do {\
    struct aws_byte_cursor cursor; \
    cursor.ptr = (uint8_t *)&cursor; \
    cursor.len = (cursorlen); \
    struct aws_byte_cursor rv = advance(&cursor, (advlen)); \
    ASSERT_NULL(rv.ptr, "advance(cursorlen=%s, advlen=%s) should fail", \
        #cursorlen, #advlen); \
    ASSERT_UINT_EQUALS(0, rv.len, "advance(cursorlen=%s, advlen=%s) should fail", \
        #cursorlen, #advlen); \
} while (0)

#define ASSERT_ADVANCE(advlen, cursorlen) do {\
    uint8_t *orig_cursor; \
    struct aws_byte_cursor cursor; \
    cursor.len = (cursorlen); \
    cursor.ptr = orig_cursor = malloc(cursor.len); \
    if (!cursor.ptr) { abort(); } \
    struct aws_byte_cursor rv = advance(&cursor, (advlen)); \
    ASSERT_PTR_EQUALS(orig_cursor, rv.ptr, "Wrong ptr in advance(cursorlen=%s, advlen=%s)", \
        #cursorlen, #advlen); \
    ASSERT_PTR_EQUALS(orig_cursor + (advlen), cursor.ptr, "Wrong new cursorptr in advance"); \
    ASSERT_UINT_EQUALS((advlen), rv.len, "Wrong returned length"); \
    ASSERT_UINT_EQUALS((cursorlen) - (advlen), cursor.len, "Wrong residual length"); \
    free(orig_cursor); \
} while (0)

static int test_byte_cursor_advance_internal(
    struct aws_byte_cursor (*advance)(struct aws_byte_cursor *cursor, size_t len)
) {
    ASSERT_ADVANCE(0, 1);
    ASSERT_ADVANCE(1, 1);
    ASSERT_NOADVANCE(2, 1);

    ASSERT_ADVANCE(4, 5);
    ASSERT_ADVANCE(5, 5);
    ASSERT_NOADVANCE(6, 5);

    ASSERT_NOADVANCE(SSIZE_MAX + 1, SSIZE_MAX);
    ASSERT_NOADVANCE(SSIZE_MAX, SSIZE_MAX + 1);

    return 0;
}

static int test_byte_cursor_advance_fn(struct aws_allocator *alloc, void *ctx) {
    return test_byte_cursor_advance_internal(aws_byte_cursor_advance);
}

static int test_byte_cursor_advance_nospec_fn(struct aws_allocator *alloc, void *ctx) {
    return test_byte_cursor_advance_internal(aws_byte_cursor_advance_nospec);
}

AWS_TEST_CASE(test_byte_cursor_advance, test_byte_cursor_advance_fn)
AWS_TEST_CASE(test_byte_cursor_advance_nospec, test_byte_cursor_advance_nospec_fn)
