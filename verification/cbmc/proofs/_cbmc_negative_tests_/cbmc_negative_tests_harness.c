/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

/**
 * A basic negative assertion should fail
 * if CBMC was run at all.
 */
void assert_check() {
    assert(1 == 0);
}

/**
 * A negative test for --bounds-check flag
 */
void bounds_check() {
    char test[10];
    test[12] = 'x';
}

/**
 * A negative test for --conversion-check flag
 */
void conversion_check() {
    unsigned long src;
    unsigned dst = src;
}

/**
 * A negative test for --div-by-zero-check flag
 */
void div_by_zero_check() {
    int test = 1 / 0;
}

/**
 * A negative test for --float-overflow-check flag
 */
void float_overflow_check() {
    float test;
    test = test + 1.0;
}

/**
 * A negative test for --nan-check flag
 */
void nan_check() {
    float test = 0.0 / 0.0;
}

/**
 * A negative test for --pointer-check flag
 */
void pointer_check() {
    int *src;
    int test = *src;
}

/**
 * A negative test for --pointer-overflow-check flag
 */
void pointer_overflow_check() {
    int offset;
    char *test;
    test = test + offset;
}

/**
 * A negative test for --pointer-primitive-check flag
 */
void pointer_primitive_check() {
    char *test;
    assert(__CPROVER_r_ok(test, 10));
}

/**
 * A negative test for --signed-overflow-check flag
 */
void signed_overflow_check() {
    int test;
    test = test + 1;
}

/**
 * A negative test for --undefined-shift-check flag
 */
void undefined_shift_check() {
    int dist;
    int test = 1 << dist;
}

/**
 * A negative test for --unsigned-overflow-check flag
 */
void unsigned_overflow_check() {
    unsigned test;
    test = test + 1;
}

void cbmc_negative_tests_harness() {
    assert_check();
    bounds_check();
    conversion_check();
    div_by_zero_check();
    float_overflow_check();
    nan_check();
    pointer_check();
    pointer_overflow_check();
    pointer_primitive_check();
    signed_overflow_check();
    undefined_shift_check();
    unsigned_overflow_check();
}
