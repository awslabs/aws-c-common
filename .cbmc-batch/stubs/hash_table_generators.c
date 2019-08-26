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

#include <aws/common/private/hash_table_impl.h>
#include <proof_helpers/make_common_data_structures.h>
#include <proof_helpers/nondet.h>
#include <proof_helpers/proof_allocators.h>

/* This file contains generators useful in hash-table stubs. See
 * aws_hash_table_non_slots_override.c and aws_hash_iter_overrides.c for how these are used
 */

/**
 * The common case for the hash-table is that it maps strings to strings. This generates
 * fully non-deterministic strings for both key and value
 */
void hash_iterator_string_string_generator(struct aws_hash_iter *new_iter, const struct aws_hash_iter *old_iter) {
    (void)old_iter;
    if (new_iter->status == AWS_HASH_ITER_STATUS_READY_FOR_USE) {
        new_iter->element.key = ensure_string_is_allocated_nondet_length();
        new_iter->element.value = ensure_string_is_allocated_nondet_length();
    }
}

/**
 * The common case for the hash-table is that it maps strings to strings. This generates
 * fully non-deterministic strings for both key and value
 */
void hash_find_string_string_generator(
    const struct aws_hash_table *map,
    const void *key,
    struct aws_hash_element *p_elem) {
    p_elem->key = ensure_string_is_allocated_nondet_length();
    p_elem->value = ensure_string_is_allocated_nondet_length();
}

/**
 * The common case for the hash-table is that it maps strings to strings.
 * Some code (for e.g. the aws_cryptosdk_enc_ctx_size() function in the ESDK uses the string header
 * but not the actual string itself.  So this allocates the header, but not the string.
 * This ensures that no successful proof CAN use the bytes of the string.
 */
void hash_iterator_unbacked_string_string_generator(
    struct aws_hash_iter *new_iter,
    const struct aws_hash_iter *old_iter) {
    (void)old_iter;
    if (new_iter->status == AWS_HASH_ITER_STATUS_READY_FOR_USE) {
        new_iter->element.key = bounded_malloc(sizeof(struct aws_string));
        new_iter->element.value = bounded_malloc(sizeof(struct aws_string));
    }
}

/**
 * The common case for the hash-table is that it maps strings to strings.
 * Some code (for e.g. the aws_cryptosdk_enc_ctx_size() function in the ESDK uses the string header
 * but not the actual string itself.  So this allocates the header, but not the string.
 * This ensures that no successful proof CAN use the bytes of the string.
 */
void hash_find_unbacked_string_string_generator(
    const struct aws_hash_table *map,
    const void *key,
    struct aws_hash_element *p_elem) {
    p_elem->key = bounded_malloc(sizeof(struct aws_string));
    p_elem->value = bounded_malloc(sizeof(struct aws_string));
}
