/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#pragma once

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

/**
 * Non-determinstic functions used in CBMC proofs
 */
bool nondet_bool(void);
int nondet_int(void);
size_t nondet_size_t(void);
uint16_t nondet_uint16_t(void);
uint32_t nondet_uint32_t(void);
uint64_t nondet_uint64_t(void);
uint8_t nondet_uint8_t(void);
void *nondet_voidp(void);
