#ifndef AWS_COMMON_PRIVATE_HASH_TABLE_H
#define AWS_COMMON_PRIVATE_HASH_TABLE_H

/*
 * Copyright 2010-2019 Amazon.com, Inc. or its affiliates. All Rights Reserved.
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

/*
 * The private implementation for the hash_table defined in aws/common/hash_table.h
 * This should not be relied upon by consumers of the library
 */

#include <aws/common/hash_table.h>

struct hash_table_entry {
    struct aws_hash_element element;
    uint64_t hash_code; /* hash code (0 signals empty) */
};

struct hash_table_state {
    aws_hash_fn *hash_fn;
    aws_hash_callback_eq_fn *equals_fn;
    aws_hash_callback_destroy_fn *destroy_key_fn;
    aws_hash_callback_destroy_fn *destroy_value_fn;
    struct aws_allocator *alloc;

    size_t size, entry_count;
    size_t max_load;
    /* We AND a hash value with mask to get the slot index */
    size_t mask;
    double max_load_factor;
    /* actually variable length */
    struct hash_table_entry slots[1];
};

AWS_STATIC uint64_t s_hash_for(struct hash_table_state *state, const void *key);

AWS_STATIC size_t s_index_for(struct hash_table_state *map, struct hash_table_entry *entry);

/* Given a header template, allocates space for a hash table of the appropriate
 * size, and copies the state header into this allocated memory, which is
 * returned.
 */
AWS_STATIC struct hash_table_state *s_alloc_state(const struct hash_table_state *template);

/* Computes the correct size and max_load based on a requested size. */
AWS_STATIC int s_update_template_size(struct hash_table_state *template, size_t expected_elements);

/* Tries to find where the requested key is or where it should go if put.
 * Returns AWS_ERROR_SUCCESS if the item existed (leaving it in *entry),
 * or AWS_ERROR_HASHTBL_ITEM_NOT_FOUND if it did not (putting its destination
 * in *entry). Note that this does not take care of displacing whatever was in
 * that entry before.
 *
 * probe_idx is set to the probe index of the entry found.
 */
AWS_STATIC int s_find_entry1(
    struct hash_table_state *state,
    uint64_t hash_code,
    const void *key,
    struct hash_table_entry **p_entry,
    size_t *p_probe_idx);

/* Inlined fast path: Check the first slot, only. */
/* TODO: Force inlining? */
AWS_STATIC int inline s_find_entry(
    struct hash_table_state *state,
    uint64_t hash_code,
    const void *key,
    struct hash_table_entry **p_entry,
    size_t *p_probe_idx);

/*
 * Attempts to find a home for the given entry. Returns after doing nothing if
 * entry was not occupied.
 */
AWS_STATIC struct hash_table_entry *s_emplace_item(
    struct hash_table_state *state,
    struct hash_table_entry entry,
    size_t probe_idx);

AWS_STATIC int s_expand_table(struct aws_hash_table *map);

/* Clears an entry. Does _not_ invoke destructor callbacks.
 * Returns the last slot touched (note that if we wrap, we'll report an index
 * lower than the original entry's index)
 */
AWS_STATIC size_t s_remove_entry(struct hash_table_state *state, struct hash_table_entry *entry);

AWS_STATIC_IMPL void s_get_next_element(struct aws_hash_iter *iter, size_t start_slot);

#endif /* AWS_COMMON_PRIVATE_HASH_TABLE_H */
