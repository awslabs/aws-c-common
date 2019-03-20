/*
 * Copyright 2019 Amazon.com, Inc. or its affiliates. All Rights Reserved.
 *
 * Licensed under the Apache License, Version 2.0 (the "License"). You may not use
 * this file except in compliance with the License. A copy of the License is
 * located at
 *
 *     http://aws.amazon.com/apache2.0/
 *
 * or in the "license" file accompanying this file. This file is distributed on an
 * "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or
 * implied. See the License for the specific language governing permissions and
 * limitations under the License.
 */

#include <proof_helpers/utils.h>

void assert_bytes_match(const uint8_t *a, const uint8_t *b, size_t len) {
    if (len > 0) {
        size_t i;
        __CPROVER_assume(i < len);
        assert(a[i] == b[i]);
    }
}

void assert_all_bytes_are(const uint8_t *a, const uint8_t c, size_t len) {
    if (len > 0) {
        size_t i;
        __CPROVER_assume(i < len);
        assert(a[i] == c);
    }
}

void assert_all_zeroes(const uint8_t *a, size_t len) {
    assert_all_bytes_are(a, 0, len);
}
