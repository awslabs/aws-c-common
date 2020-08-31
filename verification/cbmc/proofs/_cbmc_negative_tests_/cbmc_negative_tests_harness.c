/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

void bounds_check() {
    assert(1 == 0);
}

void conversion_check() {
    assert(1 == 0);
}

void div_by_zero_check() {
    assert(1 == 0);
}

void float_overflow_check() {
    assert(1 == 0);
}

void nan_check() {
    assert(1 == 0);
}

void pointer_check() {
    assert(1 == 0);
}

void pointer_overflow_check() {
    assert(1 == 0);
}

void pointer_primitive_check() {
    assert(1 == 0);
}

void signed_overflow_check() {
    assert(1 == 0);
}

void undefined_shift_check() {
    assert(1 == 0);
}

void unsigned_overflow_check() {
    assert(1 == 0);
}

void cbmc_negative_tests_harness() {
    /**
     * A basic negative assertion should fail
     * if CBMC was run at all.
     */
    assert_check();

    /**
     * A negative test for --bounds-check flag
     */
    bounds_check();

    /**
     * A negative test for --conversion-check flag
     */
    conversion_check();

    /**
     * A negative test for --div_by_zero-check flag
     */
    div_by_zero_check();

    /**
     * A negative test for --float-overflow-check flag
     */
    float_overflow_check();

    /**
     * A negative test for --nan-check flag
     */
    nan_check();

    /**
     * A negative test for --pointer-check flag
     */
    pointer_check();

    /**
     * A negative test for --pointer-overflow-check flag
     */
    pointer_overflow_check();

    /**
     * A negative test for --pointer-primitive-check flag
     */
    pointer_primitive_check();

    /**
     * A negative test for --signed-overflow-check flag
     */
    signed_overflow_check();

    /**
     * A negative test for --undefined-shift-check flag
     */
    undefined_shift_check();

    /**
     * A negative test for --unsigned-overflow-check flag
     */
    unsigned_overflow_check();
}
