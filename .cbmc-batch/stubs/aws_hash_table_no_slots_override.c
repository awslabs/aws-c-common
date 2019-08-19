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

#include <proof_helpers/nondet.h>
#include <proof_helpers/proof_allocators.h>

/********************************************************************************
 * This module represents a hash-table that is not backed by any actual memory
 * It just takes non-det actions when given inputs. We know this is safe because
 * we've already proven the c-common hash-table memory safe under these
 * pre/post conditions.
 *
 * Since we're making almost everything nondet, the only externally visible property
 * of the hash-table is the [entry_count].
 */

/**
 * As noted above the only externally visible property of the hash-table is the [entry_count]. And it can vary between
 * 0-SIZE_MAX.  So there is really nothing to assert here */
bool aws_hash_table_is_valid(const struct aws_hash_table *map) {
    return map && map->p_impl;
}

/**
 * The allocator for the hash_table
 */
void make_hash_table_with_no_backing_store(struct aws_hash_table *map, size_t max_table_entries) {
    /* Allocate a hash_table_state with no memory for the slots.
     * This ensures that if I actually try to use the slots, CBMC will throw a fit.
     */
    map->p_impl = bounded_malloc(sizeof(struct hash_table_state));
    __CPROVER_assume(map->p_impl->entry_count <= max_table_entries);
}
/**
 * Nondet clear.  Since the only externally visible property of this
 * table is the entry_count, just set it to 0
 */
void aws_hash_table_clear(struct aws_hash_table *map) {
    AWS_PRECONDITION(aws_hash_table_is_valid(map));
    struct hash_table_state *state = map->p_impl;
    state->entry_count = 0;
    AWS_POSTCONDITION(aws_hash_table_is_valid(map));
}

/**
 * Nondet put.  Since there is no backing store, we just non-determinstically either add it or don't.
 */
int aws_hash_table_put(struct aws_hash_table *map, const void *key, void *value, int *was_created) {
    AWS_PRECONDITION(aws_hash_table_is_valid(map));

    int track_was_created;
    if (was_created) {
        *was_created = track_was_created;
    }

    int rval;

    struct hash_table_state *state = map->p_impl;

    /* Avoid overflow */
    if (state->entry_count == SIZE_MAX) {
        return track_was_created ? AWS_OP_ERR : rval;
    }

    if (rval == AWS_OP_SUCCESS) {
        state->entry_count++;
    }
    AWS_POSTCONDITION(aws_hash_table_is_valid(map));
    return rval;
}

/**
 * Not yet implemented
 */
int aws_hash_table_remove_element(struct aws_hash_table *map, struct aws_hash_element *p_value);

/**
 * Not yet implemented
 */
int aws_hash_table_remove(
    struct aws_hash_table *map,
    const void *key,
    struct aws_hash_element *p_value,
    int *was_present);

/**
 * Not yet implemented
 */
int aws_hash_table_create(
    struct aws_hash_table *map,
    const void *key,
    struct aws_hash_element **p_elem,
    int *was_created);

/**
 * Implements a version of aws_hash_table_find() that non-determinstially either:
 *   1. Return NULL, indicating that the element didn't exist
 *   2. Returns a newly created element.  By default, just create a totally non-determinstic element.
 *      However, if the consumer of the stub uses the element, this may be insufficient.  Use the same
 *      style of generator as the hash_iterator stubs, except with a different signature due to the different
 *      calling context.
 *
 * To declare a genarator:
 * -DHASH_TABLE_FIND_ELEMENT_GENERATOR=the_generator_fn, where the_generator_fn has signature:
 *   the_generator_fnconst struct aws_hash_table *map, const void *key, struct aws_hash_element *p_elem).
 *
 * NOTE: If you want a version of aws_hash_table_find() that implements it be assuming the value on
 * the slot matched the value returned, that can be found in [aws_hash_table_find_override.c]
 */
#ifdef HASH_TABLE_FIND_ELEMENT_GENERATOR
void HASH_TABLE_FIND_ELEMENT_GENERATOR(
    const struct aws_hash_table *map,
    const void *key,
    struct aws_hash_element *p_elem);
#endif

int aws_hash_table_find(const struct aws_hash_table *map, const void *key, struct aws_hash_element **p_elem) {
    AWS_PRECONDITION(aws_hash_table_is_valid(map), "Input hash_table [map] must be valid.");
    AWS_PRECONDITION(AWS_OBJECT_PTR_IS_WRITABLE(p_elem), "Input pointer [p_elem] must be writable.");
    const struct hash_table_state *const state = map->p_impl;
    if (nondet_bool()) {
        *p_elem = NULL;
    } else {
        *p_elem = malloc(sizeof(struct aws_hash_element));
#ifdef HASH_TABLE_FIND_ELEMENT_GENERATOR
        HASH_TABLE_FIND_ELEMENT_GENERATOR(map, key, *p_elem);
#endif
    }
    AWS_POSTCONDITION(aws_hash_table_is_valid(map), "Output hash_table [map] must be valid.");
    return AWS_OP_SUCCESS;
}
