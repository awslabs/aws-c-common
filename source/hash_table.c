/*
 * Copyright 2010-2017 Amazon.com, Inc. or its affiliates. All Rights Reserved.
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

/* For more information on how the RH hash works and in particular how we do
 * deletions, see:
 * http://codecapsule.com/2013/11/17/robin-hood-hashing-backward-shift-deletion/
 */

#include <aws/common/hash_table.h>
#include <aws/common/math.h>
#include <aws/common/private/hash_table_impl.h>
#include <aws/common/string.h>

#include <limits.h>
#include <stdio.h>
#include <stdlib.h>

/* Include lookup3.c so we can (potentially) inline it and make use of the mix()
 * macro. */
#include <aws/common/private/lookup3.c>

static void s_suppress_unused_lookup3_func_warnings(void) {
    /* We avoid making changes to lookup3 if we can avoid it, but since it has functions
     * we're not using, reference them somewhere to suppress the unused function warning.
     */
    (void)hashword;
    (void)hashword2;
    (void)hashlittle;
    (void)hashbig;
}

/**
 * Calculate the hash for the given key.
 * Ensures a reasonable semantics for null keys.
 * Ensures that no object ever hashes to 0, which is the sentinal value for an empty hash element.
 */
static uint64_t s_hash_for(struct hash_table_state *state, const void *key) {
    AWS_PRECONDITION(hash_table_state_is_valid(state));
    s_suppress_unused_lookup3_func_warnings();

    if (key == NULL) {
        /* The best answer */
        return 42;
    }

    uint64_t hash_code = state->hash_fn(key);
    if (!hash_code) {
        hash_code = 1;
    }
    AWS_POSTCONDITION(hash_code != 0);
    return hash_code;
}

/**
 * Check equality of two objects, with a reasonable semantics for null.
 */
static bool s_safe_eq_check(aws_hash_callback_eq_fn *equals_fn, const void *a, const void *b) {
    /* Short circuit if the pointers are the same */
    if (a == b) {
        return true;
    }
    /* If one but not both are null, the objects are not equal */
    if (a == NULL || b == NULL) {
        return false;
    }
    /* If both are non-null, call the underlying equals fn */
    return equals_fn(a, b);
}

/**
 * Check equality of two hash keys, with a reasonable semantics for null keys.
 */
static bool s_hash_keys_eq(struct hash_table_state *state, const void *a, const void *b) {
    AWS_PRECONDITION(hash_table_state_is_valid(state));
    bool rval = s_safe_eq_check(state->equals_fn, a, b);
    AWS_POSTCONDITION(hash_table_state_is_valid(state));
    return rval;
}

static size_t s_index_for(struct hash_table_state *map, struct hash_table_entry *entry) {
    AWS_PRECONDITION(hash_table_state_is_valid(map));
    size_t index = entry - map->slots;
    AWS_POSTCONDITION(index < map->size);
    AWS_PRECONDITION(hash_table_state_is_valid(map));
    return index;
}

#if 0
/* Useful debugging code for anyone working on this in the future */
static uint64_t s_distance(struct hash_table_state *state, int index) {
    return (index - state->slots[index].hash_code) & state->mask;
}

void hash_dump(struct aws_hash_table *tbl) {
    struct hash_table_state *state = tbl->p_impl;

    printf("Dumping hash table contents:\n");

    for (int i = 0; i < state->size; i++) {
        printf("%7d: ", i);
        struct hash_table_entry *e = &state->slots[i];
        if (!e->hash_code) {
            printf("EMPTY\n");
        } else {
            printf("k: %p v: %p hash_code: %lld displacement: %lld\n",
                e->element.key, e->element.value, e->hash_code,
                (i - e->hash_code) & state->mask);
        }
    }
}
#endif

#if 0
/* Not currently exposed as an API. Should we have something like this? Useful for benchmarks */
AWS_COMMON_API
void aws_hash_table_print_stats(struct aws_hash_table *table) {
    struct hash_table_state *state = table->p_impl;
    uint64_t total_disp = 0;
    uint64_t max_disp = 0;

    printf("\n=== Hash table statistics ===\n");
    printf("Table size: %zu/%zu (max load %zu, remaining %zu)\n", state->entry_count, state->size, state->max_load, state->max_load - state->entry_count);
    printf("Load factor: %02.2lf%% (max %02.2lf%%)\n",
        100.0 * ((double)state->entry_count / (double)state->size),
        state->max_load_factor);

    for (size_t i = 0; i < state->size; i++) {
        if (state->slots[i].hash_code) {
            int displacement = distance(state, i);
            total_disp += displacement;
            if (displacement > max_disp) {
                max_disp = displacement;
            }
        }
    }

    size_t *disp_counts = calloc(sizeof(*disp_counts), max_disp + 1);

    for (size_t i = 0; i < state->size; i++) {
        if (state->slots[i].hash_code) {
            disp_counts[distance(state, i)]++;
        }
    }

    uint64_t median = 0;
    uint64_t passed = 0;
    for (uint64_t i = 0; i <= max_disp && passed < total_disp / 2; i++) {
        median = i;
        passed += disp_counts[i];
    }

    printf("Displacement statistics: Avg %02.2lf max %llu median %llu\n", (double)total_disp / (double)state->entry_count, max_disp, median);
    for (uint64_t i = 0; i <= max_disp; i++) {
        printf("Displacement %2lld: %zu entries\n", i, disp_counts[i]);
    }
    free(disp_counts);
    printf("\n");
}
#endif

size_t aws_hash_table_get_entry_count(const struct aws_hash_table *map) {
    struct hash_table_state *state = map->p_impl;
    return state->entry_count;
}

/* Given a header template, allocates space for a hash table of the appropriate
 * size, and copies the state header into this allocated memory, which is
 * returned.
 */
static struct hash_table_state *s_alloc_state(const struct hash_table_state *template) {
    size_t required_bytes;
    if (hash_table_state_required_bytes(template->size, &required_bytes)) {
        return NULL;
    }

    /* An empty slot has hashcode 0. So this marks all slots as empty */
    struct hash_table_state *state = aws_mem_calloc(template->alloc, 1, required_bytes);

    if (state == NULL) {
        return state;
    }

    *state = *template;
    return state;
}

/* Computes the correct size and max_load based on a requested size. */
static int s_update_template_size(struct hash_table_state *template, size_t expected_elements) {
    size_t min_size = expected_elements;

    if (min_size < 2) {
        min_size = 2;
    }

    /* size is always a power of 2 */
    size_t size;
    if (aws_round_up_to_power_of_two(min_size, &size)) {
        return AWS_OP_ERR;
    }

    /* Update the template once we've calculated everything successfully */
    template->size = size;
    template->max_load = (size_t)(template->max_load_factor * (double)template->size);
    /* Ensure that there is always at least one empty slot in the hash table */
    if (template->max_load >= size) {
        template->max_load = size - 1;
    }

    /* Since size is a power of 2: (index & (size - 1)) == (index % size) */
    template->mask = size - 1;

    return AWS_OP_SUCCESS;
}

int aws_hash_table_init(
    struct aws_hash_table *map,
    struct aws_allocator *alloc,
    size_t size,
    aws_hash_fn *hash_fn,
    aws_hash_callback_eq_fn *equals_fn,
    aws_hash_callback_destroy_fn *destroy_key_fn,
    aws_hash_callback_destroy_fn *destroy_value_fn) {
    AWS_PRECONDITION(map && alloc && hash_fn && equals_fn);

    struct hash_table_state template;
    template.hash_fn = hash_fn;
    template.equals_fn = equals_fn;
    template.destroy_key_fn = destroy_key_fn;
    template.destroy_value_fn = destroy_value_fn;
    template.alloc = alloc;

    template.entry_count = 0;
    template.max_load_factor = 0.95; /* TODO - make configurable? */

    if (s_update_template_size(&template, size)) {
        return AWS_OP_ERR;
    }
    map->p_impl = s_alloc_state(&template);

    if (!map->p_impl) {
        return AWS_OP_ERR;
    }

    AWS_POSTCONDITION(aws_hash_table_is_valid(map));
    return AWS_OP_SUCCESS;
}

void aws_hash_table_clean_up(struct aws_hash_table *map) {
    AWS_PRECONDITION(map);
    AWS_PRECONDITION(map->p_impl == NULL || aws_hash_table_is_valid(map));
    struct hash_table_state *state = map->p_impl;

    /* Ensure that we're idempotent */
    if (!state) {
        return;
    }

    aws_hash_table_clear(map);
    aws_mem_release(map->p_impl->alloc, map->p_impl);

    map->p_impl = NULL;
    AWS_POSTCONDITION(map->p_impl == NULL);
}

void aws_hash_table_swap(struct aws_hash_table *AWS_RESTRICT a, struct aws_hash_table *AWS_RESTRICT b) {
    AWS_PRECONDITION(a != b);
    struct aws_hash_table tmp = *a;
    *a = *b;
    *b = tmp;
}

void aws_hash_table_move(struct aws_hash_table *AWS_RESTRICT to, struct aws_hash_table *AWS_RESTRICT from) {
    AWS_PRECONDITION(to != NULL && from != NULL && to != from && aws_hash_table_is_valid(from));
    *to = *from;
    AWS_ZERO_STRUCT(*from);
    AWS_POSTCONDITION(aws_hash_table_is_valid(to));
}

/* Tries to find where the requested key is or where it should go if put.
 * Returns AWS_ERROR_SUCCESS if the item existed (leaving it in *entry),
 * or AWS_ERROR_HASHTBL_ITEM_NOT_FOUND if it did not (putting its destination
 * in *entry). Note that this does not take care of displacing whatever was in
 * that entry before.
 *
 * probe_idx is set to the probe index of the entry found.
 */

static int s_find_entry1(
    struct hash_table_state *state,
    uint64_t hash_code,
    const void *key,
    struct hash_table_entry **p_entry,
    size_t *p_probe_idx);

/* Inlined fast path: Check the first slot, only. */
/* TODO: Force inlining? */
static int inline s_find_entry(
    struct hash_table_state *state,
    uint64_t hash_code,
    const void *key,
    struct hash_table_entry **p_entry,
    size_t *p_probe_idx) {
    struct hash_table_entry *entry = &state->slots[hash_code & state->mask];

    if (entry->hash_code == 0) {
        if (p_probe_idx) {
            *p_probe_idx = 0;
        }
        *p_entry = entry;
        return AWS_ERROR_HASHTBL_ITEM_NOT_FOUND;
    }

    if (entry->hash_code == hash_code && s_hash_keys_eq(state, key, entry->element.key)) {
        if (p_probe_idx) {
            *p_probe_idx = 0;
        }
        *p_entry = entry;
        return AWS_OP_SUCCESS;
    }

    return s_find_entry1(state, hash_code, key, p_entry, p_probe_idx);
}

static int s_find_entry1(
    struct hash_table_state *state,
    uint64_t hash_code,
    const void *key,
    struct hash_table_entry **p_entry,
    size_t *p_probe_idx) {
    size_t probe_idx = 1;
    /* If we find a deleted entry, we record that index and return it as our probe index (i.e. we'll keep searching to
     * see if it already exists, but if not we'll overwrite the deleted entry).
     */

    int rv;
    struct hash_table_entry *entry;
    /* This loop is guaranteed to terminate because entry_probe is bounded above by state->mask (i.e. state->size - 1).
     * Since probe_idx increments every loop iteration, it will become larger than entry_probe after at most state->size
     * transitions and the loop will exit (if it hasn't already)
     */
    while (1) {
#pragma CPROVER check push
#pragma CPROVER check disable "unsigned-overflow"
        uint64_t index = (hash_code + probe_idx) & state->mask;
#pragma CPROVER check pop
        entry = &state->slots[index];
        if (!entry->hash_code) {
            rv = AWS_ERROR_HASHTBL_ITEM_NOT_FOUND;
            break;
        }

        if (entry->hash_code == hash_code && s_hash_keys_eq(state, key, entry->element.key)) {
            rv = AWS_ERROR_SUCCESS;
            break;
        }

#pragma CPROVER check push
#pragma CPROVER check disable "unsigned-overflow"
        uint64_t entry_probe = (index - entry->hash_code) & state->mask;
#pragma CPROVER check pop

        if (entry_probe < probe_idx) {
            /* We now know that our target entry cannot exist; if it did exist,
             * it would be at the current location as it has a higher probe
             * length than the entry we are examining and thus would have
             * preempted that item
             */
            rv = AWS_ERROR_HASHTBL_ITEM_NOT_FOUND;
            break;
        }

        probe_idx++;
    }

    *p_entry = entry;
    if (p_probe_idx) {
        *p_probe_idx = probe_idx;
    }

    return rv;
}

int aws_hash_table_find(const struct aws_hash_table *map, const void *key, struct aws_hash_element **p_elem) {

    AWS_PRECONDITION(aws_hash_table_is_valid(map));
    AWS_PRECONDITION(AWS_OBJECT_PTR_IS_WRITABLE(p_elem));

    struct hash_table_state *state = map->p_impl;
    uint64_t hash_code = s_hash_for(state, key);
    struct hash_table_entry *entry;

    int rv = s_find_entry(state, hash_code, key, &entry, NULL);

    if (rv == AWS_ERROR_SUCCESS) {
        *p_elem = &entry->element;
    } else {
        *p_elem = NULL;
    }
    AWS_POSTCONDITION(aws_hash_table_is_valid(map));
    return AWS_OP_SUCCESS;
}

/**
 * Attempts to find a home for the given entry.
 * If the entry was empty (i.e. hash-code of 0), then the function does nothing and returns NULL
 * Otherwise, it emplaces the item, and returns a pointer to the newly emplaced entry.
 * This function is only called after the hash-table has been expanded to fit the new element,
 * so it should never fail.
 */
static struct hash_table_entry *s_emplace_item(
    struct hash_table_state *state,
    struct hash_table_entry entry,
    size_t probe_idx) {
    AWS_PRECONDITION(hash_table_state_is_valid(state));

    if (entry.hash_code == 0) {
        AWS_POSTCONDITION(hash_table_state_is_valid(state));
        return NULL;
    }

    struct hash_table_entry *rval = NULL;

    /* Since a valid hash_table has at least one empty element, this loop will always terminate in at most linear time
     */
    while (entry.hash_code != 0) {
#pragma CPROVER check push
#pragma CPROVER check disable "unsigned-overflow"
        size_t index = (size_t)(entry.hash_code + probe_idx) & state->mask;
#pragma CPROVER check pop
        struct hash_table_entry *victim = &state->slots[index];

#pragma CPROVER check push
#pragma CPROVER check disable "unsigned-overflow"
        size_t victim_probe_idx = (size_t)(index - victim->hash_code) & state->mask;
#pragma CPROVER check pop

        if (!victim->hash_code || victim_probe_idx < probe_idx) {
            /* The first thing we emplace is the entry itself. A pointer to its location becomes the rval */
            if (!rval) {
                rval = victim;
            }

            struct hash_table_entry tmp = *victim;
            *victim = entry;
            entry = tmp;

            probe_idx = victim_probe_idx + 1;
        } else {
            probe_idx++;
        }
    }

    AWS_POSTCONDITION(hash_table_state_is_valid(state));
    AWS_POSTCONDITION(rval >= &state->slots[0] && rval < &state->slots[state->size]);
    return rval;
}

static int s_expand_table(struct aws_hash_table *map) {
    struct hash_table_state *old_state = map->p_impl;
    struct hash_table_state template = *old_state;

    size_t new_size;
    if (aws_mul_size_checked(template.size, 2, &new_size)) {
        return AWS_OP_ERR;
    }

    if (s_update_template_size(&template, new_size)) {
        return AWS_OP_ERR;
    }

    struct hash_table_state *new_state = s_alloc_state(&template);
    if (!new_state) {
        return AWS_OP_ERR;
    }

    for (size_t i = 0; i < old_state->size; i++) {
        struct hash_table_entry entry = old_state->slots[i];
        if (entry.hash_code) {
            /* We can directly emplace since we know we won't put the same item twice */
            s_emplace_item(new_state, entry, 0);
        }
    }

    map->p_impl = new_state;
    aws_mem_release(new_state->alloc, old_state);

    return AWS_OP_SUCCESS;
}

int aws_hash_table_create(
    struct aws_hash_table *map,
    const void *key,
    struct aws_hash_element **p_elem,
    int *was_created) {

    struct hash_table_state *state = map->p_impl;
    uint64_t hash_code = s_hash_for(state, key);
    struct hash_table_entry *entry;
    size_t probe_idx;
    int ignored;
    if (!was_created) {
        was_created = &ignored;
    }

    int rv = s_find_entry(state, hash_code, key, &entry, &probe_idx);

    if (rv == AWS_ERROR_SUCCESS) {
        if (p_elem) {
            *p_elem = &entry->element;
        }
        *was_created = 0;
        return AWS_OP_SUCCESS;
    }

    /* Okay, we need to add an entry. Check the load factor first. */
    size_t incr_entry_count;
    if (aws_add_size_checked(state->entry_count, 1, &incr_entry_count)) {
        return AWS_OP_ERR;
    }
    if (incr_entry_count > state->max_load) {
        rv = s_expand_table(map);
        if (rv != AWS_OP_SUCCESS) {
            /* Any error was already raised in expand_table */
            return rv;
        }
        state = map->p_impl;
        /* If we expanded the table, we need to discard the probe index returned from find_entry,
         * as it's likely that we can find a more desirable slot. If we don't, then later gets will
         * terminate before reaching our probe index.

         * n.b. currently we ignore this probe_idx subsequently, but leaving
         this here so we don't
         * forget when we optimize later. */
        probe_idx = 0;
    }

    state->entry_count++;
    struct hash_table_entry new_entry;
    new_entry.element.key = key;
    new_entry.element.value = NULL;
    new_entry.hash_code = hash_code;

    entry = s_emplace_item(state, new_entry, probe_idx);

    if (p_elem) {
        *p_elem = &entry->element;
    }

    *was_created = 1;

    return AWS_OP_SUCCESS;
}

AWS_COMMON_API
int aws_hash_table_put(struct aws_hash_table *map, const void *key, void *value, int *was_created) {
    struct aws_hash_element *p_elem;
    int was_created_fallback;

    if (!was_created) {
        was_created = &was_created_fallback;
    }

    if (aws_hash_table_create(map, key, &p_elem, was_created)) {
        return AWS_OP_ERR;
    }

    /*
     * aws_hash_table_create might resize the table, which results in map->p_impl changing.
     * It is therefore important to wait to read p_impl until after we return.
     */
    struct hash_table_state *state = map->p_impl;

    if (!*was_created) {
        if (p_elem->key != key && state->destroy_key_fn) {
            state->destroy_key_fn((void *)p_elem->key);
        }

        if (state->destroy_value_fn) {
            state->destroy_value_fn((void *)p_elem->value);
        }
    }

    p_elem->key = key;
    p_elem->value = value;

    return AWS_OP_SUCCESS;
}

/* Clears an entry. Does _not_ invoke destructor callbacks.
 * Returns the last slot touched (note that if we wrap, we'll report an index
 * lower than the original entry's index)
 */
static size_t s_remove_entry(struct hash_table_state *state, struct hash_table_entry *entry) {
    AWS_PRECONDITION(hash_table_state_is_valid(state));
    AWS_PRECONDITION(state->entry_count > 0);
    AWS_PRECONDITION(entry >= &state->slots[0] && entry < &state->slots[state->size]);
    state->entry_count--;

    /* Shift subsequent entries back until we find an entry that belongs at its
     * current position. This is important to ensure that subsequent searches
     * don't terminate at the removed element.
     */
    size_t index = s_index_for(state, entry);
    /* There is always at least one empty slot in the hash table, so this loop always terminates */
    while (1) {
        size_t next_index = (index + 1) & state->mask;

        /* If we hit an empty slot, stop */
        if (!state->slots[next_index].hash_code) {
            break;
        }
        /* If the next slot is at the start of the probe sequence, stop.
         * We know that nothing with an earlier home slot is after this;
         * otherwise this index-zero entry would have been evicted from its
         * home.
         */
        if ((state->slots[next_index].hash_code & state->mask) == next_index) {
            break;
        }

        /* Okay, shift this one back */
        state->slots[index] = state->slots[next_index];
        index = next_index;
    }

    /* Clear the entry we shifted out of */
    AWS_ZERO_STRUCT(state->slots[index]);
    AWS_POSTCONDITION(hash_table_state_is_valid(state));
    AWS_POSTCONDITION(index <= state->size);
    return index;
}

int aws_hash_table_remove(
    struct aws_hash_table *map,
    const void *key,
    struct aws_hash_element *p_value,
    int *was_present) {

    struct hash_table_state *state = map->p_impl;
    uint64_t hash_code = s_hash_for(state, key);
    struct hash_table_entry *entry;
    int ignored;

    if (!was_present) {
        was_present = &ignored;
    }

    int rv = s_find_entry(state, hash_code, key, &entry, NULL);

    if (rv != AWS_ERROR_SUCCESS) {
        *was_present = 0;
        return AWS_OP_SUCCESS;
    }

    *was_present = 1;

    if (p_value) {
        *p_value = entry->element;
    } else {
        if (state->destroy_key_fn) {
            state->destroy_key_fn((void *)entry->element.key);
        }
        if (state->destroy_value_fn) {
            state->destroy_value_fn(entry->element.value);
        }
    }
    s_remove_entry(state, entry);

    return AWS_OP_SUCCESS;
}

int aws_hash_table_foreach(
    struct aws_hash_table *map,
    int (*callback)(void *context, struct aws_hash_element *pElement),
    void *context) {

    for (struct aws_hash_iter iter = aws_hash_iter_begin(map); !aws_hash_iter_done(&iter); aws_hash_iter_next(&iter)) {
        int rv = callback(context, &iter.element);

        if (rv & AWS_COMMON_HASH_TABLE_ITER_DELETE) {
            aws_hash_iter_delete(&iter, false);
        }

        if (!(rv & AWS_COMMON_HASH_TABLE_ITER_CONTINUE)) {
            break;
        }
    }

    return AWS_OP_SUCCESS;
}

bool aws_hash_table_eq(
    const struct aws_hash_table *a,
    const struct aws_hash_table *b,
    aws_hash_callback_eq_fn *value_eq) {
    AWS_PRECONDITION(aws_hash_table_is_valid(a));
    AWS_PRECONDITION(aws_hash_table_is_valid(b));
    AWS_PRECONDITION(value_eq != NULL);

    if (aws_hash_table_get_entry_count(a) != aws_hash_table_get_entry_count(b)) {
        AWS_POSTCONDITION(aws_hash_table_is_valid(a));
        AWS_POSTCONDITION(aws_hash_table_is_valid(b));

        return false;
    }

    /*
     * Now that we have established that the two tables have the same number of
     * entries, we can simply iterate one and compare against the same key in
     * the other.
     */
    for (size_t i = 0; i < a->p_impl->size; ++i) {
        const struct hash_table_entry *const a_entry = &a->p_impl->slots[i];
        if (a_entry->hash_code == 0) {
            continue;
        }

        struct aws_hash_element *b_element = NULL;

        aws_hash_table_find(b, a_entry->element.key, &b_element);

        if (!b_element) {
            /* Key is present in A only */
            AWS_POSTCONDITION(aws_hash_table_is_valid(a));
            AWS_POSTCONDITION(aws_hash_table_is_valid(b));
            return false;
        }

        if (!s_safe_eq_check(value_eq, a_entry->element.value, b_element->value)) {
            AWS_POSTCONDITION(aws_hash_table_is_valid(a));
            AWS_POSTCONDITION(aws_hash_table_is_valid(b));
            return false;
        }
    }
    AWS_POSTCONDITION(aws_hash_table_is_valid(a));
    AWS_POSTCONDITION(aws_hash_table_is_valid(b));
    return true;
}

/**
 * Given an iterator, and a start slot, find the next available filled slot if it exists
 * Otherwise, return an iter that will return true for aws_hash_iter_done().
 * Note that aws_hash_iter_is_valid() need not hold on entry to the function, since
 * it can be called on a partially constructed iter from aws_hash_iter_begin().
 *
 * Note that calling this on an iterator which is "done" is idempotent: it will return another
 * iterator which is "done".
 */
static inline void s_get_next_element(struct aws_hash_iter *iter, size_t start_slot) {
    AWS_PRECONDITION(iter != NULL);
    struct hash_table_state *state = iter->map->p_impl;
    size_t limit = iter->limit;

    for (size_t i = start_slot; i < limit; i++) {
        struct hash_table_entry *entry = &state->slots[i];

        if (entry->hash_code) {
            iter->element = entry->element;
            iter->slot = i;
            iter->status = AWS_HASH_ITER_STATUS_READY_FOR_USE;
            return;
        }
    }
    iter->element.key = NULL;
    iter->element.value = NULL;
    iter->slot = iter->limit;
    iter->status = AWS_HASH_ITER_STATUS_DONE;
    AWS_POSTCONDITION(aws_hash_iter_is_valid(iter));
}

struct aws_hash_iter aws_hash_iter_begin(const struct aws_hash_table *map) {
    AWS_PRECONDITION(aws_hash_table_is_valid(map));
    struct hash_table_state *state = map->p_impl;
    struct aws_hash_iter iter;
    AWS_ZERO_STRUCT(iter);
    iter.map = map;
    iter.limit = state->size;
    s_get_next_element(&iter, 0);
    AWS_POSTCONDITION(iter.status == AWS_HASH_ITER_STATUS_DONE || iter.status == AWS_HASH_ITER_STATUS_READY_FOR_USE);
    AWS_POSTCONDITION(aws_hash_iter_is_valid(&iter));
    return iter;
}

bool aws_hash_iter_done(const struct aws_hash_iter *iter) {
    AWS_PRECONDITION(aws_hash_iter_is_valid(iter));
    AWS_PRECONDITION(iter->status == AWS_HASH_ITER_STATUS_DONE || iter->status == AWS_HASH_ITER_STATUS_READY_FOR_USE);
    /*
     * SIZE_MAX is a valid (non-terminal) value for iter->slot in the event that
     * we delete slot 0. See comments in aws_hash_iter_delete.
     *
     * As such we must use == rather than >= here.
     */
    bool rval = (iter->slot == iter->limit);
    AWS_POSTCONDITION(iter->status == AWS_HASH_ITER_STATUS_DONE || iter->status == AWS_HASH_ITER_STATUS_READY_FOR_USE);
    AWS_POSTCONDITION(rval == (iter->status == AWS_HASH_ITER_STATUS_DONE));
    AWS_POSTCONDITION(aws_hash_iter_is_valid(iter));
    return rval;
}

void aws_hash_iter_next(struct aws_hash_iter *iter) {
    AWS_PRECONDITION(aws_hash_iter_is_valid(iter));
#pragma CPROVER check push
#pragma CPROVER check disable "unsigned-overflow"
    s_get_next_element(iter, iter->slot + 1);
#pragma CPROVER check pop
    AWS_POSTCONDITION(iter->status == AWS_HASH_ITER_STATUS_DONE || iter->status == AWS_HASH_ITER_STATUS_READY_FOR_USE);
    AWS_POSTCONDITION(aws_hash_iter_is_valid(iter));
}

void aws_hash_iter_delete(struct aws_hash_iter *iter, bool destroy_contents) {
    AWS_PRECONDITION(iter->status == AWS_HASH_ITER_STATUS_READY_FOR_USE);
    AWS_PRECONDITION(aws_hash_iter_is_valid(iter));
    AWS_PRECONDITION(iter->map->p_impl->entry_count > 0);

    struct hash_table_state *state = iter->map->p_impl;
    if (destroy_contents) {
        if (state->destroy_key_fn) {
            state->destroy_key_fn((void *)iter->element.key);
        }
        if (state->destroy_value_fn) {
            state->destroy_value_fn(iter->element.value);
        }
    }

    size_t last_index = s_remove_entry(state, &state->slots[iter->slot]);

    /* If we shifted elements that are not part of the window we intend to iterate
     * over, it means we shifted an element that we already visited into the
     * iter->limit - 1 position. To avoid double iteration, we'll now reduce the
     * limit to compensate.
     *
     * Note that last_index cannot equal iter->slot, because slots[iter->slot]
     * is empty before we start walking the table.
     */
    if (last_index < iter->slot || last_index >= iter->limit) {
        iter->limit--;
    }

    /*
     * After removing this entry, the next entry might be in the same slot, or
     * in some later slot, or we might have no further entries.
     *
     * We also expect that the caller will call aws_hash_iter_done and aws_hash_iter_next
     * after this delete call. This gets a bit tricky if we just deleted the value
     * in slot 0, and a new value has shifted in.
     *
     * To deal with this, we'll just step back one slot, and let _next start iteration
     * at our current slot. Note that if we just deleted slot 0, this will result in
     * underflowing to SIZE_MAX; we have to take care in aws_hash_iter_done to avoid
     * treating this as an end-of-iteration condition.
     */
#pragma CPROVER check push
#pragma CPROVER check disable "unsigned-overflow"
    iter->slot--;
#pragma CPROVER check pop
    iter->status = AWS_HASH_ITER_STATUS_DELETE_CALLED;
    AWS_POSTCONDITION(iter->status == AWS_HASH_ITER_STATUS_DELETE_CALLED);
    AWS_POSTCONDITION(aws_hash_iter_is_valid(iter));
}

void aws_hash_table_clear(struct aws_hash_table *map) {
    AWS_PRECONDITION(aws_hash_table_is_valid(map));
    struct hash_table_state *state = map->p_impl;

    /* Check that we have at least one destructor before iterating over the table */
    if (state->destroy_key_fn || state->destroy_value_fn) {
        for (size_t i = 0; i < state->size; ++i) {
            struct hash_table_entry *entry = &state->slots[i];
            if (!entry->hash_code) {
                continue;
            }
            if (state->destroy_key_fn) {
                state->destroy_key_fn((void *)entry->element.key);
            }
            if (state->destroy_value_fn) {
                state->destroy_value_fn(entry->element.value);
            }
        }
    }
    /* Since hash code 0 represents an empty slot we can just zero out the
     * entire table. */
    memset(state->slots, 0, sizeof(*state->slots) * state->size);

    state->entry_count = 0;
    AWS_POSTCONDITION(aws_hash_table_is_valid(map));
}

uint64_t aws_hash_c_string(const void *item) {
    const char *str = item;

    /* first digits of pi in hex */
    uint32_t b = 0x3243F6A8, c = 0x885A308D;
    hashlittle2(str, strlen(str), &c, &b);

    return ((uint64_t)b << 32) | c;
}

uint64_t aws_hash_string(const void *item) {
    const struct aws_string *str = item;

    /* first digits of pi in hex */
    uint32_t b = 0x3243F6A8, c = 0x885A308D;
    hashlittle2(aws_string_bytes(str), str->len, &c, &b);

    return ((uint64_t)b << 32) | c;
}

uint64_t aws_hash_byte_cursor_ptr(const void *item) {
    const struct aws_byte_cursor *cur = item;

    /* first digits of pi in hex */
    uint32_t b = 0x3243F6A8, c = 0x885A308D;
    hashlittle2(cur->ptr, cur->len, &c, &b);

    return ((uint64_t)b << 32) | c;
}

uint64_t aws_hash_ptr(const void *item) {
    /* first digits of e in hex
     * 2.b7e 1516 28ae d2a6 */
    uint32_t b = 0x2b7e1516, c = 0x28aed2a6;

    hashlittle2(&item, sizeof(item), &c, &b);

    return ((uint64_t)b << 32) | c;
}

bool aws_hash_callback_c_str_eq(const void *a, const void *b) {
    AWS_PRECONDITION(aws_c_string_is_valid(a));
    AWS_PRECONDITION(aws_c_string_is_valid(b));
    bool rval = !strcmp(a, b);
    AWS_POSTCONDITION(aws_c_string_is_valid(a));
    AWS_POSTCONDITION(aws_c_string_is_valid(b));
    return rval;
}

bool aws_hash_callback_string_eq(const void *a, const void *b) {
    AWS_PRECONDITION(aws_string_is_valid(a));
    AWS_PRECONDITION(aws_string_is_valid(b));
    bool rval = aws_string_eq(a, b);
    AWS_POSTCONDITION(aws_string_is_valid(a));
    AWS_POSTCONDITION(aws_string_is_valid(b));
    return rval;
}

void aws_hash_callback_string_destroy(void *a) {
    AWS_PRECONDITION(aws_string_is_valid(a));
    aws_string_destroy(a);
}

bool aws_ptr_eq(const void *a, const void *b) {
    return a == b;
}
