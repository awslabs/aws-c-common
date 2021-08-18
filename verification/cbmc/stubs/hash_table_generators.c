/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/common/private/hash_table_impl.h>
#include <proof_helpers/make_common_data_structures.h>
#include <proof_helpers/nondet.h>

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
        __CPROVER_assume(aws_string_is_valid(new_iter->element.key));
        new_iter->element.value = ensure_string_is_allocated_nondet_length();
        __CPROVER_assume(aws_string_is_valid(new_iter->element.value));
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
    if (p_elem) {
        p_elem->key = ensure_string_is_allocated_nondet_length();
        __CPROVER_assume(aws_string_is_valid(p_elem->key));
        p_elem->value = ensure_string_is_allocated_nondet_length();
        __CPROVER_assume(aws_string_is_valid(p_elem->value));
    }
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
        new_iter->element.key = malloc(sizeof(struct aws_string));
        new_iter->element.value = malloc(sizeof(struct aws_string));
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
    p_elem->key = malloc(sizeof(struct aws_string));
    p_elem->value = malloc(sizeof(struct aws_string));
}
