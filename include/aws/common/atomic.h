#ifndef AWS_COMMON_ATOMIC_H
#define AWS_COMMON_ATOMIC_H

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

/**
 * Atomically retrieves the value at `dst`, and returns it.
 */
static inline int aws_atomic_load(int *dst);

/**
 * Atomically sets the value at `dst` to `value`. Returns the previous value at `dst`.
 */
static inline int aws_atomic_store(int *dst, int value);

/**
 * Adds `addend` to `dst` and returns the old value from `dst`.
 */
static inline int aws_atomic_add(int *dst, int addend);

/**
 * Sets `dst` to `value` if `compare` equals `dst`. If `dst` is set to the new value, the return value is true. Otherwise
 * the return value is false, and `compare` is assigned to the old value at `dst`.
 */
static inline bool aws_atomic_compare_exchange(int *dst, int *compare, int value);

/**
 * Atomically retrieves the value at `dst`.
 */
static inline void *aws_atomic_load_ptr(void **dst);

/**
 * Atomically sets the value at `dst` to `value`. Returns the previous value at `dst`.
 */
static inline void *aws_atomic_store_ptr(void **dst, void *value);

/**
 * Sets `dst` to `value` if `compare` equals `dst`. Returns the old value at `dst`.
 */
static inline bool aws_atomic_compare_exchange_ptr(void **dst, void **compare, void *value);

#include <aws/common/atomic.inl>

#endif /* AWS_COMMON_ATOMIC_H */
