/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/common/private/hash_table_impl.h>
#include <proof_helpers/nondet.h>

/********************************************************************************
 * This module represents a hash-table that is not backed by any actual memory
 * It just takes non-det actions when given inputs. We know this is safe because
 * we've already proven the c-common hash-table memory safe under these
 * pre/post conditions.
 *
 * Since we're making almost everything nondet, the only externally visible property
 * of the hash-table is the entry_count.
 */

/**
 * As noted above the only externally visible property of the hash-table is the [entry_count]. And it can vary between
 * 0-SIZE_MAX.  So there is really nothing to assert here */
bool aws_hash_table_is_valid(const struct aws_hash_table *map) {
    return map && map->p_impl;
}

/**
 * Given a pointer to a hash_iter, checks that it is well-formed, with all data-structure invariants.
 */
bool aws_hash_iter_is_valid(const struct aws_hash_iter *iter) {
    if (!iter) {
        return false;
    }
    if (!iter->map) {
        return false;
    }
    if (!aws_hash_table_is_valid(iter->map)) {
        return false;
    }
    if (iter->limit != iter->map->p_impl->entry_count) {
        return false;
    }

    switch (iter->status) {
        case AWS_HASH_ITER_STATUS_DONE:
            /* Done iff slot == limit */
            return iter->slot == iter->limit;
        case AWS_HASH_ITER_STATUS_DELETE_CALLED:
            /* iter->slot can underflow to SIZE_MAX after a delete
             * see the comments for aws_hash_iter_delete() */
            return iter->slot <= iter->limit;
        case AWS_HASH_ITER_STATUS_READY_FOR_USE:
            /* A slot must point to a valid location (i.e. hash_code != 0) */
            return iter->slot < iter->limit;
    }
    /* Invalid status code */
    return false;
}

/**
 * Allocate a hash_table_state with no memory for the slots.
 * Since CBMC runs with memory safety assertions on,
 * CBMC will detect any attempt to use the slots.
 * This ensures that no code will ever accidentally use the values
 * in the slots, ensuring maximal nondeterminism.
 */
void make_hash_table_with_no_backing_store(struct aws_hash_table *map, size_t max_table_entries) {
    if (map != NULL) {
        map->p_impl = malloc(sizeof(struct hash_table_state));
        __CPROVER_assume(map->p_impl != NULL);
        __CPROVER_assume(map->p_impl->entry_count <= max_table_entries);
    }
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
 * NOTE: If you want a version of aws_hash_table_find() that that ensures that the table actually has the found value
 * when find returns success, that can be found in aws_hash_table_find_override.c
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

#ifdef HASH_ITER_ELEMENT_GENERATOR
void HASH_ITER_ELEMENT_GENERATOR(struct aws_hash_iter *new_iter, const struct aws_hash_iter *old_iter);
#endif

/* Simple map for what the iterator does: it just chugs along, returns a nondet value, until its gone at most
 * map->entry_count times */
struct aws_hash_iter aws_hash_iter_begin(const struct aws_hash_table *map) {
    /* Leave it as non-det as possible */
    AWS_PRECONDITION(aws_hash_table_is_valid(map));

    /* Build a nondet iterator, set the required fields, and return it */
    struct aws_hash_iter rval;
    rval.map = map;
    rval.limit = map->p_impl->entry_count;
    rval.slot = 0;
    rval.status = (rval.slot == rval.limit) ? AWS_HASH_ITER_STATUS_DONE : AWS_HASH_ITER_STATUS_READY_FOR_USE;
#ifdef HASH_ITER_ELEMENT_GENERATOR
    HASH_ITER_ELEMENT_GENERATOR(&rval, NULL);
#endif
    return rval;
}

bool aws_hash_iter_done(const struct aws_hash_iter *iter) {
    AWS_PRECONDITION(aws_hash_iter_is_valid(iter));
    AWS_PRECONDITION(
        iter->status == AWS_HASH_ITER_STATUS_DONE || iter->status == AWS_HASH_ITER_STATUS_READY_FOR_USE,
        "Input aws_hash_iter [iter] status should either be done or ready to use.");
    bool rval = iter->slot == iter->limit;
    assert(rval == (iter->status == AWS_HASH_ITER_STATUS_DONE));
    return rval;
}

void aws_hash_iter_next(struct aws_hash_iter *iter) {
    AWS_PRECONDITION(aws_hash_iter_is_valid(iter));

    if (iter->slot == iter->limit) {
        iter->status = AWS_HASH_ITER_STATUS_DONE;
        return;
    }

    /* Build a nondet iterator, set the required fields, and copy it over */
    struct aws_hash_iter rval;
    rval.map = iter->map;
    rval.limit = iter->limit;
    rval.slot = iter->slot + 1;
    rval.status = (rval.slot == rval.limit) ? AWS_HASH_ITER_STATUS_DONE : AWS_HASH_ITER_STATUS_READY_FOR_USE;
#ifdef HASH_ITER_ELEMENT_GENERATOR
    HASH_ITER_ELEMENT_GENERATOR(&rval, iter);
#endif

    *iter = rval;
}

/* delete always leaves the element unusable, so we'll just leave the element totally nondet */
void aws_hash_iter_delete(struct aws_hash_iter *iter, bool destroy_contents) {
    AWS_PRECONDITION(aws_hash_iter_is_valid(iter));
    AWS_PRECONDITION(
        iter->status == AWS_HASH_ITER_STATUS_READY_FOR_USE, "Input aws_hash_iter [iter] must be ready for use.");
    AWS_PRECONDITION(aws_hash_iter_is_valid(iter));
    AWS_PRECONDITION(
        iter->map->p_impl->entry_count > 0,
        "The hash_table_state pointed by input [iter] must contain at least one entry.");

    /* reduce the size of the underlying map */
    iter->map->p_impl->entry_count--;

    /* Build a nondet iterator, set the required fields, and copy it over */
    struct aws_hash_iter rval;
    rval.map = iter->map;
    rval.slot = iter->slot;
    rval.limit = iter->limit - 1;
    rval.status = AWS_HASH_ITER_STATUS_DELETE_CALLED;
    *iter = rval;
}
