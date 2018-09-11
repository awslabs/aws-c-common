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

#include <intrin.h>
#include <stdint.h>
#include <stdlib.h>

#if !(defined(_M_IX86) || defined(_M_X64))
#    error Atomics are not currently supported for non-x86 MSVC platforms

/*
 * In particular, it's not clear that seq_cst will work properly on non-x86
 * memory models
 */

#endif

/**
 * Some general notes:
 *
 * Windows automatically uses acquire semantics for read accesses to volatile variables,
 * and release semantics for stores. Volatile to volatile references are ordered.
 *
 * Interlocked* functions implicitly have acq_rel semantics; there are ones with weaker
 * semantics as well, but because windows is generally used on x86, where there's not a lot
 * of performance difference between different ordering modes anyway, we just use the stronger
 * forms for now. Further, on x86, they actually have seq_cst semantics as they use locked instructions.
 *
 * Since all loads and stores are acq and/or rel already, we can do non-seq_cst loads and stores
 * as just volatile variable accesses.
 *
 * For seq_cst accesses, we take advantage of the facts that:
 * 1. Loads are not reordered with other loads
 * 2. Stores are not reordered with other stores
 * 3. Locked instructions (including swaps) have a total order
 * 4. Non-locked accesses are not reordered with locked instructions
 *
 * Therefore, if we ensure that all seq_cst stores are locked, we can establish
 * a total order on stores, and the intervening ordinary loads will not violate that total
 * order.
 * See http://www.cs.cmu.edu/~410-f10/doc/Intel_Reordering_318147.pdf 2.7, which covers
 * this use case.
 */

#pragma warning(push)
#pragma warning(disable : 4201) /* nameless union */

struct aws_atomic_var {
    union {
        size_t intval;
        void *ptrval;
    };
};

#pragma warning(pop)

static inline void aws_atomic_priv_check_order(enum aws_memory_order order) {
#ifndef NDEBUG
    switch (order) {
        case aws_memory_order_relaxed:
            return;
        case aws_memory_order_acquire:
            return;
        case aws_memory_order_release:
            return;
        case aws_memory_order_acq_rel:
            return;
        case aws_memory_order_seq_cst:
            return;
        default: /* Unknown memory order */
            abort();
    }
#endif
    (void)order;
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
size_t aws_atomic_load_int_explicit(
    volatile const struct aws_atomic_var *var,
    enum aws_memory_order memory_order) {
    aws_atomic_priv_check_order(memory_order);
    return var->intval;
}

/**
 * Reads an atomic var as an pointer, using the specified ordering, and returns the result.
 */
AWS_STATIC_IMPL
void *aws_atomic_load_ptr_explicit(volatile const struct aws_atomic_var *var, enum aws_memory_order memory_order) {
    aws_atomic_priv_check_order(memory_order);
    return var->ptrval;
}

/**
 * Stores an integer into an atomic var, using the specified ordering.
 */
AWS_STATIC_IMPL
void aws_atomic_store_int_explicit(
    volatile struct aws_atomic_var *var,
    size_t n,
    enum aws_memory_order memory_order) {
    aws_atomic_priv_check_order(memory_order);
    if (memory_order != aws_memory_order_seq_cst) {
        var->intval = n;
    } else {
        InterlockedExchange64(&var->intval, n);
    }
}

/**
 * Stores an pointer into an atomic var, using the specified ordering.
 */
AWS_STATIC_IMPL
void aws_atomic_store_ptr_explicit(volatile struct aws_atomic_var *var, void *p, enum aws_memory_order memory_order) {
    aws_atomic_priv_check_order(memory_order);
    if (memory_order != aws_memory_order_seq_cst) {
        var->ptrval = p;
    } else {
        InterlockedExchangePointer(&var->ptrval, p);
    }
}

/**
 * Exchanges an integer with the value in an atomic_var, using the specified ordering.
 * Returns the value that was previously in the atomic_var.
 */
AWS_STATIC_IMPL
size_t aws_atomic_exchange_int_explicit(
    volatile struct aws_atomic_var *var,
    size_t n,
    enum aws_memory_order memory_order) {
    aws_atomic_priv_check_order(memory_order);
    return InterlockedExchange64(&var->intval, n);
}

/**
 * Exchanges a pointer with the value in an atomic_var, using the specified ordering.
 * Returns the value that was previously in the atomic_var.
 */
AWS_STATIC_IMPL
void *aws_atomic_exchange_ptr_explicit(volatile struct aws_atomic_var *var, void *p, enum aws_memory_order memory_order) {
    aws_atomic_priv_check_order(memory_order);
    return InterlockedExchangePointer(&var->ptrval, p);
}

/**
 * Atomically compares *var to *expected; if they are equal, atomically sets *var = desired. Otherwise, *expected is set
 * to the value in *var. On success, the memory ordering used was order_success; otherwise, it was order_failure.
 * order_failure must be no stronger than order_success, and must not be release or acq_rel.
 */
AWS_STATIC_IMPL
bool aws_atomic_compare_exchange_int_explicit(
    volatile struct aws_atomic_var *var,
    size_t *expected,
    size_t desired,
    enum aws_memory_order order_success,
    enum aws_memory_order order_failure) {
    aws_atomic_priv_check_order(order_success);
    aws_atomic_priv_check_order(order_failure);

    size_t oldval = InterlockedCompareExchange64(&var->intval, desired, *expected);
    bool successful = oldval == *expected;
    *expected = oldval;

    return successful;
}

/**
 * Atomically compares *var to *expected; if they are equal, atomically sets *var = desired. Otherwise, *expected is set
 * to the value in *var. On success, the memory ordering used was order_success; otherwise, it was order_failure.
 * order_failure must be no stronger than order_success, and must not be release or acq_rel.
 */
AWS_STATIC_IMPL
bool aws_atomic_compare_exchange_ptr_explicit(
    volatile struct aws_atomic_var *var,
    void **expected,
    void *desired,
    enum aws_memory_order order_success,
    enum aws_memory_order order_failure) {
    aws_atomic_priv_check_order(order_success);
    aws_atomic_priv_check_order(order_failure);

    void *oldval = InterlockedCompareExchangePointer(&var->ptrval, desired, *expected);
    bool successful = oldval == *expected;
    *expected = oldval;

    return successful;
}

/**
 * Atomically adds n to *var, and returns the previous value of *var.
 */
AWS_STATIC_IMPL
size_t aws_atomic_fetch_add_explicit(
    volatile struct aws_atomic_var *var,
    size_t n,
    enum aws_memory_order order) {
    aws_atomic_priv_check_order(order);

    return InterlockedExchangeAdd64(&var->intval, n);
}

/**
 * Atomically subtracts n from *var, and returns the previous value of *var.
 */
AWS_STATIC_IMPL
size_t aws_atomic_fetch_sub_explicit(
    volatile struct aws_atomic_var *var,
    size_t n,
    enum aws_memory_order order) {
    aws_atomic_priv_check_order(order);

    return InterlockedExchangeAdd64(&var->intval, -n);
}

/**
 * Atomically ORs n with *var, and returns the previous value of *var.
 */
AWS_STATIC_IMPL
size_t aws_atomic_fetch_or_explicit(
    volatile struct aws_atomic_var *var,
    size_t n,
    enum aws_memory_order order) {
    aws_atomic_priv_check_order(order);

    return InterlockedOr64(&var->intval, n);
}

/**
 * Atomically ANDs n with *var, and returns the previous value of *var.
 */
AWS_STATIC_IMPL
size_t aws_atomic_fetch_and_explicit(
    volatile struct aws_atomic_var *var,
    size_t n,
    enum aws_memory_order order) {
    aws_atomic_priv_check_order(order);

    return InterlockedAnd64(&var->intval, n);
}

/**
 * Atomically XORs n with *var, and returns the previous value of *var.
 */
AWS_STATIC_IMPL
size_t aws_atomic_fetch_xor_explicit(
    volatile struct aws_atomic_var *var,
    size_t n,
    enum aws_memory_order order) {
    aws_atomic_priv_check_order(order);

    return InterlockedXor64(&var->intval, n);
}

/**
 * Provides the same reordering guarantees as an atomic operation with the specified memory order, without
 * needing to actually perform an atomic operation.
 */
AWS_STATIC_IMPL
void aws_atomic_thread_fence(enum aws_memory_order order) {
    volatile int x = 0;
    aws_atomic_priv_check_order(order);

    switch (order) {
        case aws_memory_order_seq_cst:
            MemoryBarrier();
            break;
        case aws_memory_order_release:
        case aws_memory_order_acquire:
        case aws_memory_order_acq_rel:
            x = x;
            break;
        case aws_memory_order_relaxed:
            /* no-op */
            break;
    }
}

#define AWS_ATOMICS_HAVE_THREAD_FENCE
