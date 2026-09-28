#ifndef AWS_COMMON_PRIVATE_EXTERNAL_MODULE_IMPL_H
#define AWS_COMMON_PRIVATE_EXTERNAL_MODULE_IMPL_H

/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/common/common.h>

/**
 * Initializes the JSON module for use.
 * @param allocator The allocator to use for creating aws_json_value structs.
 */
void aws_json_module_init(struct aws_allocator *allocator);

/**
 * Cleans up the JSON module. Should be called when finished using the module.
 */
void aws_json_module_cleanup(void);

void aws_cbor_module_init(struct aws_allocator *allocator);

void aws_cbor_module_cleanup(void);

/**
 * Caches the CPU feature detection used by the base64 encoder/decoder.
 * Called from aws_common_library_init() while still single-threaded, so
 * concurrent base64 calls don't race on the lazy detection in cpuid.c.
 */
void aws_encoding_module_init(void);

#endif // AWS_COMMON_PRIVATE_EXTERNAL_MODULE_IMPL_H
