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

/* These are implicitly included, but helps with editor highlighting */
#include <aws/common/atomics.h>
#include <aws/common/common.h>

#include <stdint.h>
#include <stdlib.h>

#ifdef __clang__
#    pragma clang diagnostic push
#    pragma clang diagnostic ignored "-Wc11-extensions"
#endif

struct aws_atomic_var {
    union {
        size_t intval;
        void *ptrval;
    };
};

static inline int aws_atomic_priv_xlate_order(enum aws_memory_order order) {
    switch (order) {
        case aws_memory_order_relaxed:
            return __ATOMIC_RELAXED;
        case aws_memory_order_acquire:
            return __ATOMIC_ACQUIRE;
        case aws_memory_order_release:
            return __ATOMIC_RELEASE;
        case aws_memory_order_acq_rel:
            return __ATOMIC_ACQ_REL;
        case aws_memory_order_seq_cst:
            return __ATOMIC_SEQ_CST;
        default: /* Unknown memory order */
            abort();
    }
}

/**
 * Initializes an atomic variable with an integer value. This operation should be done before any
 * other operations on this atomic variable, and must be done before attempting any parallel operations.
 */
void aws_atomic_init_int(volatile struct aws_atomic_var *var, size_t n) {
    var->intval = n;
}

/**
 * Initializes an atomic variable with a pointer value. This operation should be done before any
 * other operations on this atomic variable, and must be done before attempting any parallel operations.
 */
void aws_atomic_init_ptr(volatile struct aws_atomic_var *var, void *p) {
    var->ptrval = p;
}

/**
 * Reads an atomic var as an integer, using the specified ordering, and returns the result.
 */
AWS_STATIC_IMPL
size_t aws_atomic_load_int(
    volatile const struct aws_atomic_var *var,
    enum aws_memory_order memory_order) {
    return __atomic_load_n(&var->intval, aws_atomic_priv_xlate_order(memory_order));
}

/**
 * Reads an atomic var as an pointer, using the specified ordering, and returns the result.
 */
AWS_STATIC_IMPL
void *aws_atomic_load_ptr(volatile const struct aws_atomic_var *var, enum aws_memory_order memory_order) {
    return __atomic_load_n(&var->ptrval, aws_atomic_priv_xlate_order(memory_order));
}

/**
 * Stores an integer into an atomic var, using the specified ordering.
 */
AWS_STATIC_IMPL
void aws_atomic_store_int(
    volatile struct aws_atomic_var *var,
    size_t n,
    enum aws_memory_order memory_order) {
    __atomic_store_n(&var->intval, n, aws_atomic_priv_xlate_order(memory_order));
}

/**
 * Stores an pointer into an atomic var, using the specified ordering.
 */
AWS_STATIC_IMPL
void aws_atomic_store_ptr(volatile struct aws_atomic_var *var, void *p, enum aws_memory_order memory_order) {
    __atomic_store_n(&var->ptrval, p, aws_atomic_priv_xlate_order(memory_order));
}

/**
 * Exchanges an integer with the value in an atomic_var, using the specified ordering.
 * Returns the value that was previously in the atomic_var.
 */
AWS_STATIC_IMPL
size_t aws_atomic_swap_int(
    volatile struct aws_atomic_var *var,
    size_t n,
    enum aws_memory_order memory_order) {
    return __atomic_exchange_n(&var->intval, n, aws_atomic_priv_xlate_order(memory_order));
}

/**
 * Exchanges a pointer with the value in an atomic_var, using the specified ordering.
 * Returns the value that was previously in the atomic_var.
 */
AWS_STATIC_IMPL
void *aws_atomic_swap_ptr(volatile struct aws_atomic_var *var, void *p, enum aws_memory_order memory_order) {
    return __atomic_exchange_n(&var->ptrval, p, aws_atomic_priv_xlate_order(memory_order));
}

/**
 * Atomically compares *var to *expected; if they are equal, atomically sets *var = desired. Otherwise, *expected is set
 * to the value in *var. On success, the memory ordering used was order_success; otherwise, it was order_failure.
 * order_failure must be no stronger than order_success, and must not be release or acq_rel.
 */
AWS_STATIC_IMPL
bool aws_atomic_compare_exchange_int(
    volatile struct aws_atomic_var *var,
    size_t *expected,
    size_t desired,
    enum aws_memory_order order_success,
    enum aws_memory_order order_failure) {
    return __atomic_compare_exchange_n(
        &var->intval,
        expected,
        desired,
        false,
        aws_atomic_priv_xlate_order(order_success),
        aws_atomic_priv_xlate_order(order_failure));
}

/**
 * Atomically compares *var to *expected; if they are equal, atomically sets *var = desired. Otherwise, *expected is set
 * to the value in *var. On success, the memory ordering used was order_success; otherwise, it was order_failure.
 * order_failure must be no stronger than order_success, and must not be release or acq_rel.
 */
AWS_STATIC_IMPL
bool aws_atomic_compare_exchange_ptr(
    volatile struct aws_atomic_var *var,
    void **expected,
    void *desired,
    enum aws_memory_order order_success,
    enum aws_memory_order order_failure) {
    return __atomic_compare_exchange_n(
        &var->ptrval,
        expected,
        desired,
        false,
        aws_atomic_priv_xlate_order(order_success),
        aws_atomic_priv_xlate_order(order_failure));
}

/**
 * Atomically adds n to *var, and returns the previous value of *var.
 */
AWS_STATIC_IMPL
size_t aws_atomic_fetch_add(
    volatile struct aws_atomic_var *var,
    size_t n,
    enum aws_memory_order order) {
    return __atomic_fetch_add(&var->intval, n, aws_atomic_priv_xlate_order(order));
}

/**
 * Atomically subtracts n from *var, and returns the previous value of *var.
 */
AWS_STATIC_IMPL
size_t aws_atomic_fetch_sub(
    volatile struct aws_atomic_var *var,
    size_t n,
    enum aws_memory_order order) {
    return __atomic_fetch_sub(&var->intval, n, aws_atomic_priv_xlate_order(order));
}

/**
 * Atomically ORs n with *var, and returns the previous value of *var.
 */
AWS_STATIC_IMPL
size_t aws_atomic_fetch_or(
    volatile struct aws_atomic_var *var,
    size_t n,
    enum aws_memory_order order) {
    return __atomic_fetch_or(&var->intval, n, aws_atomic_priv_xlate_order(order));
}

/**
 * Atomically ANDs n with *var, and returns the previous value of *var.
 */
AWS_STATIC_IMPL
size_t aws_atomic_fetch_and(
    volatile struct aws_atomic_var *var,
    size_t n,
    enum aws_memory_order order) {
    return __atomic_fetch_and(&var->intval, n, aws_atomic_priv_xlate_order(order));
}

/**
 * Atomically XORs n with *var, and returns the previous value of *var.
 */
AWS_STATIC_IMPL
size_t aws_atomic_fetch_xor(
    volatile struct aws_atomic_var *var,
    size_t n,
    enum aws_memory_order order) {
    return __atomic_fetch_xor(&var->intval, n, aws_atomic_priv_xlate_order(order));
}

/**
 * Provides the same reordering guarantees as an atomic operation with the specified memory order, without
 * needing to actually perform an atomic operation.
 */
AWS_STATIC_IMPL
void aws_atomic_thread_fence(enum aws_memory_order order) {
    __atomic_thread_fence(order);
}

#ifdef __clang__
#    pragma clang diagnostic pop
#endif

#define AWS_ATOMICS_HAVE_THREAD_FENCE
