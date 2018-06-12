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
#include <aws/common/string.h>
#include <stdlib.h>
#include <stdio.h>
#include <limits.h>

/* Include lookup3.c so we can (potentially) inline it and make use of the mix() macro. */
#include <aws/common/private/lookup3.c>

static void suppress_unused_lookup3_func_warnings() {
    /* We avoid making changes to lookup3 if we can avoid it, but since it has functions
     * we're not using, reference them somewhere to suppress the unused function warning.
     */
    (void)hashword;
    (void)hashword2;
    (void)hashlittle;
    (void)hashbig;
}

struct hash_table_entry {
    struct aws_hash_element element;
    uint64_t hash_code; /* hash code (0 signals empty) */
};

struct hash_table_state {
    aws_hash_fn_t hash_fn;
    aws_equals_fn_t equals_fn;
    aws_hash_element_destroy_t destroy_key_fn;
    aws_hash_element_destroy_t destroy_value_fn;
    struct aws_allocator *alloc;

    size_t size, entry_count;
    size_t max_load;
    /* We AND a hash value with mask to get the slot index */
    uint64_t  mask;
    double max_load_factor;
    /* actually variable length */
    struct hash_table_entry slots[1];
};

static uint64_t hash_for(struct hash_table_state *state, const void *key) {
    suppress_unused_lookup3_func_warnings();

    uint64_t hash_code = state->hash_fn(key);
    if (!hash_code) {
        hash_code = 1;
    }

    return hash_code;
}

static int index_for(struct hash_table_state *map, struct hash_table_entry *entry) {
    return (int)(entry - map->slots);
}

#if 0
/* Useful debugging code for anyone working on this in the future */
static uint64_t distance(struct hash_table_state *state, int index) {
    return (index - state->slots[index].hash_code) & state->mask;
}

void hash_dump(struct aws_hash_table *tbl) {
    struct hash_table_state *state = tbl->pImpl;

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
AWS_COMMON_API void aws_hash_table_print_stats(struct aws_hash_table *table) {
    struct hash_table_state *state = table->pImpl;
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

/* Given a header template, allocates space for a hash table of the appropriate size, and copies the state header
 * into this allocated memory, which is returned.
 */
static struct hash_table_state *alloc_state(const struct hash_table_state *template) {
    size_t elemsize;

    /* We use size - 1 because the first slot is inlined into the hash_table_state structure. */
    if (!aws_mul_size_checked(template->size - 1, sizeof(template->slots[0]), &elemsize)) {
        return NULL;
    }

    size_t size = elemsize + sizeof(*template);

    if (size < elemsize) {
        return NULL;
    }

    struct hash_table_state *state = aws_mem_acquire(template->alloc, size);

    if (state == NULL) {
        return state;
    }

    memcpy(state, template, sizeof(*template));
    memset(&state->slots[0], 0, size - sizeof(*state) + sizeof(state->slots[0]));

    return state;
}

/* Computes the correct size and max_load based on a requested size. */
static int update_template_size(struct hash_table_state *template, size_t expected_elements) {
    size_t min_size = expected_elements;

    if (min_size < 2) {
        min_size = 2;
    }

    size_t mask = ~(size_t)0, size = 1;
    while (size < min_size) {
        size = size << 1;
        mask = mask << 1;

        if (size == 0) {
            /* Overflow */
            return aws_raise_error(AWS_ERROR_OOM);
        }
    }
    mask = ~mask;

    /* Cross-check - make sure we didn't just overflow somehow. */
    if (size < expected_elements) {
        return aws_raise_error(AWS_ERROR_OOM);
    }

    template->size = size;
    template->max_load = (size_t)(template->max_load_factor * template->size);
    if (template->max_load >= size) {
        template->max_load = size - 1;
    }

    /* Make sure we don't overflow when computing memory requirements either */
    size_t required_mem = aws_mul_size_saturating(template->size, sizeof(struct hash_table_entry));
    if (required_mem == SIZE_MAX || (required_mem + sizeof(struct hash_table_state)) < required_mem) {
        return aws_raise_error(AWS_ERROR_OOM);
    }

    template->size = size;
    template->mask = mask;

    return AWS_OP_SUCCESS;
}

int aws_hash_table_init(struct aws_hash_table *map,
                        struct aws_allocator *alloc,
                        size_t size,
                        aws_hash_fn_t hash_fn,
                        aws_equals_fn_t equals_fn,
                        aws_hash_element_destroy_t destroy_key_fn,
                        aws_hash_element_destroy_t destroy_value_fn) {

    struct hash_table_state template;
    template.hash_fn = hash_fn;
    template.equals_fn = equals_fn;
    template.destroy_key_fn = destroy_key_fn;
    template.destroy_value_fn = destroy_value_fn;
    template.alloc = alloc;

    template.entry_count = 0;
    template.max_load_factor = 0.95; /* TODO - make configurable? */

    update_template_size(&template, size);
    map->pImpl = alloc_state(&template);

    if (!map->pImpl) {
        return AWS_OP_ERR;
    }

    return AWS_OP_SUCCESS;
}

void aws_hash_table_clean_up(struct aws_hash_table *map) {
    aws_hash_table_clear(map);
    aws_mem_release(((struct hash_table_state *)map->pImpl)->alloc, map->pImpl);
}

/* Tries to find where the requested key is or where it should go if put.
 * Returns AWS_ERROR_SUCCESS if the item existed (leaving it in *entry),
 * or AWS_ERROR_HASHTBL_ITEM_NOT_FOUND if it did not (putting its destination
 * in *entry). Note that this does not take care of displacing whatever was in that entry before.
 *
 * probe_idx is set to the probe index of the entry found.
 */

static int find_entry1(struct hash_table_state *state, uint64_t hash_code, const void *key, struct hash_table_entry **p_entry, int *p_probe_idx);

/* Inlined fast path: Check the first slot, only. */
/* TODO: Force inlining? */
static int inline find_entry(struct hash_table_state *state, uint64_t hash_code, const void *key, struct hash_table_entry **p_entry, int *p_probe_idx) {
    struct hash_table_entry *entry = &state->slots[hash_code & state->mask];

    if (entry->hash_code == 0) {
        if (p_probe_idx) *p_probe_idx = 0;
        *p_entry = entry;
        return AWS_ERROR_HASHTBL_ITEM_NOT_FOUND;
    }

    if (entry->hash_code == hash_code && state->equals_fn(key, entry->element.key)) {
        if (p_probe_idx) *p_probe_idx = 0;
        *p_entry = entry;
        return AWS_OP_SUCCESS;
    }

    return find_entry1(state, hash_code, key, p_entry, p_probe_idx);
}

static int find_entry1(struct hash_table_state *state, uint64_t hash_code, const void *key, struct hash_table_entry **p_entry, int *p_probe_idx) {
    int probe_idx = 1;
    /* If we find a deleted entry, we record that index and return it as our probe index (i.e. we'll keep searching to see if it already exists,
     * but if not we'll overwrite the deleted entry).
     */
    int probe_cap = INT_MAX;

    int rv;
    struct hash_table_entry *entry;
    do {
        uint64_t index = (hash_code + probe_idx) & state->mask;
        entry = &state->slots[index];
        if (!entry->hash_code) {
            rv = AWS_ERROR_HASHTBL_ITEM_NOT_FOUND;
            break;
        }

        if (entry->hash_code == hash_code && state->equals_fn(key, entry->element.key)) {
            rv = AWS_ERROR_SUCCESS;
            break;
        }

        uint64_t entry_probe = (index - entry->hash_code) & state->mask;

        if (entry_probe < probe_idx) {
            /* We now know that our target entry cannot exist; if it did exist, it would be at the current location
             * as it has a higher probe length than the entry we are examining and thus would have preempted that
             * item
             */
            rv = AWS_ERROR_HASHTBL_ITEM_NOT_FOUND;
            break;
        }

        probe_idx++;
    } while(1);

    *p_entry = entry;
    if (p_probe_idx) {
        if (probe_cap < probe_idx) {
            probe_idx = probe_cap;
        }
        *p_probe_idx = probe_idx;
    }

    return rv;
}

int aws_hash_table_find(const struct aws_hash_table *map,
    const void *key, struct aws_hash_element **pElem) {
    struct hash_table_state *state = map->pImpl;
    uint64_t hash_code = hash_for(state, key);
    struct hash_table_entry *entry;

    int rv = find_entry(state, hash_code, key, &entry, NULL);

    if (rv == AWS_ERROR_SUCCESS) {
        *pElem = &entry->element;
    } else {
        *pElem = NULL;
    }

    return AWS_OP_SUCCESS;
}

/*
 * Attempts to find a home for the given entry. Returns after doing nothing if entry was not occupied.
 */
static struct hash_table_entry *emplace_item(struct hash_table_state *state, struct hash_table_entry entry, int probe_idx) {
    struct hash_table_entry *initial_placement = NULL;

    while (entry.hash_code) {
        int index = (int)(entry.hash_code + probe_idx) & state->mask;
        struct hash_table_entry *victim = &state->slots[index];

        int victim_probe_idx = (int)(index - victim->hash_code) & state->mask;

        if (!victim->hash_code || victim_probe_idx < probe_idx) {
            if (!initial_placement) {
                initial_placement = victim;
            }

            struct hash_table_entry tmp = *victim;
            *victim = entry;
            entry = tmp;

            probe_idx = victim_probe_idx + 1;
        } else {
            probe_idx++;
        }
    }

    return initial_placement;
}

static int expand_table(struct aws_hash_table *map) {
    struct hash_table_state *old_state = map->pImpl;
    struct hash_table_state template = *old_state;

    update_template_size(&template, template.size * 2);

    struct hash_table_state *new_state = alloc_state(&template);
    if (!new_state) {
        return AWS_OP_ERR;
    }

    for (int i = 0; i < old_state->size; i++) {
        struct hash_table_entry entry = old_state->slots[i];
        if (entry.hash_code) {
            /* We can directly emplace since we know we won't put the same item twice */
            emplace_item(new_state, entry, 0);
        }
    }

    map->pImpl = new_state;
    aws_mem_release(new_state->alloc, old_state);

    return AWS_OP_SUCCESS;
}

int aws_hash_table_create(struct aws_hash_table *map,
    const void *key, struct aws_hash_element **pElem, int *was_created
) {
    struct hash_table_state *state = map->pImpl;
    uint64_t hash_code = hash_for(state, key);
    struct hash_table_entry *entry;
    int probe_idx;
    int ignored;
    if (!was_created) {
        was_created = &ignored;
    }

    int rv = find_entry(state, hash_code, key, &entry, &probe_idx);

    if (rv == AWS_ERROR_SUCCESS) {
        if (pElem) {
            *pElem = &entry->element;
        }
        *was_created = 0;
        return AWS_OP_SUCCESS;
    }

    /* Okay, we need to add an entry. Check the load factor first. */
    if (state->entry_count + 1 > state->max_load) {
        rv = expand_table(map);
        if (rv != AWS_OP_SUCCESS) {
            /* Any error was already raised in expand_table */
            return rv;
        }
        state = map->pImpl;
        /* If we expanded the table, we need to discard the probe index returned from find_entry,
         * as it's likely that we can find a more desirable slot. If we don't, then later gets will
         * terminate before reaching our probe index.

         * n.b. currently we ignore this probe_idx subsequently, but leaving this here so we don't
         * forget when we optimize later. */
        probe_idx = 0;
    }

    state->entry_count++;
    struct hash_table_entry new_entry;
    new_entry.element.key = key;
    new_entry.element.value = NULL;
    new_entry.hash_code = hash_code;

    entry = emplace_item(state, new_entry, probe_idx);

    if (pElem) {
        *pElem = &entry->element;
    }

    *was_created = 1;

    return AWS_OP_SUCCESS;
}

/* Clears an entry. Does _not_ invoke destructor callbacks.
 * Returns the last slot touched (note that if we wrap, we'll report an index lower than the
 * original entry's index)
 */
static int remove_entry(struct hash_table_state *state, struct hash_table_entry *entry) {
    state->entry_count--;

    /* Shift subsequent entries back until we find an entry that belongs at its current position.
     * This is important to ensure that subsequent searches don't terminate at the removed element.
     */
    int index = index_for(state, entry);
    while (1) {
        int next_index = (index + 1) & state->mask;

        /* If we hit an empty slot, stop */
        if (!state->slots[next_index].hash_code) break;
        /* If the next slot is at the start of the probe sequence, stop.
         * We know that nothing with an earlier home slot is after this; otherwise
         * this index-zero entry would have been evicted from its home.
         */
        if ((state->slots[next_index].hash_code & state->mask) == next_index) break;

        /* Okay, shift this one back */
        memcpy(&state->slots[index], &state->slots[next_index], sizeof(*state->slots));
        index = next_index;
    }

    /* Clear the entry we shifted out of */
    memset(&state->slots[index], 0, sizeof(*entry));

    return index;
}

int aws_hash_table_remove(struct aws_hash_table *map,
    const void *key, struct aws_hash_element *pValue,
    int *was_present
) {
    struct hash_table_state *state = map->pImpl;
    uint64_t hash_code = hash_for(state, key);
    struct hash_table_entry *entry;
    int ignored;

    if (!was_present) {
        was_present = &ignored;
    }

    int rv = find_entry(state, hash_code, key, &entry, NULL);

    if (rv != AWS_ERROR_SUCCESS) {
        *was_present = 0;
        return AWS_OP_SUCCESS;
    }

    *was_present = 1;

    if (pValue) {
        *pValue = entry->element;
    } else {
        if (state->destroy_key_fn) {
            state->destroy_key_fn((void *)entry->element.key);
        }
        if (state->destroy_value_fn) {
            state->destroy_value_fn(entry->element.value);
        }
    }
    remove_entry(state, entry);

    return AWS_OP_SUCCESS;
}

int aws_hash_table_foreach(struct aws_hash_table *map,
    int (*callback)(void *baton, struct aws_hash_element *pElement), void *baton)
{
    struct hash_table_state *state = map->pImpl;
    size_t limit = state->size;

    for (int i = 0; i < limit; i++) {
        struct hash_table_entry *entry = &state->slots[i];

        if (!entry->hash_code) {
            continue;
        }

        int rv = callback(baton, &entry->element);

        if (rv & AWS_COMMON_HASH_TABLE_ITER_DELETE) {
            int last_index = remove_entry(state, entry);
            /* Removing an entry will shift back subsequent elements,
             * so we must revisit this slot.
             */
            i--;
            /* If we shifted elements outside of our current limit, then that means
             * that (exactly) one element that we've previously visited is now inside
             * our horizon set by limit, so decrement limit to compensate
             */
            if (last_index < i || last_index >= limit) {
                limit--;
            }
        }

        if (!(rv & AWS_COMMON_HASH_TABLE_ITER_CONTINUE)) {
            break;
        }
    }

    return AWS_OP_SUCCESS;
}

void aws_hash_table_clear(struct aws_hash_table *map) {
    struct hash_table_state *state = map->pImpl;
    if (state->destroy_key_fn) {
        if (state->destroy_value_fn) {
            for (size_t i = 0; i < state->size; ++i) {
                struct hash_table_entry *entry = &state->slots[i];

                if (entry->hash_code) {
                    state->destroy_key_fn((void *)entry->element.key);
                    state->destroy_value_fn(entry->element.value);
                }
            }
        } else {
            for (size_t i = 0; i < state->size; ++i) {
                struct hash_table_entry *entry = &state->slots[i];

                if (entry->hash_code) {
                    state->destroy_key_fn((void *)entry->element.key);
                }
            }
        }
    } else if (state->destroy_value_fn) {
        for (size_t i = 0; i < state->size; ++i) {
            struct hash_table_entry *entry = &state->slots[i];

            if (entry->hash_code) {
                state->destroy_value_fn(entry->element.value);
            }
        }
    }

    /* Since hash code 0 represents an empty slot we can just zero out the entire table. */
    memset(state->slots, 0, sizeof(*state->slots) * state->size);
}

uint64_t aws_hash_c_string(const void *item) {
    const char *str = item;

    /* first digits of pi in hex */
    uint32_t b = 0x3243F6A8, c = 0x885A308D;
    hashlittle2(str, strlen(str), &c, &b);

    return ((uint64_t)b << 32) | c;
}

uint64_t aws_hash_string(const void *item) {
    const struct aws_string * str = item;

    /* first digits of pi in hex */
    uint32_t b = 0x3243F6A8, c = 0x885A308D;
    hashlittle2(aws_string_bytes(str), str->len, &c, &b);

    return ((uint64_t)b << 32) | c;
}

uint64_t aws_hash_ptr(const void *item) {
    /* first digits of e in hex
     * 2.b7e 1516 28ae d2a6 */
    uint32_t b = 0x2b7e1516, c = 0x28aed2a6;

    hashlittle2(&item, sizeof(item), &c, &b);

    return ((uint64_t)b << 32) | c;
}

bool aws_c_string_eq(const void *a, const void *b) {
    return !strcmp((const char *)a, (const char *)b);
}

bool aws_string_eq(const void *a, const void *b) {
    const struct aws_string * str_a = a;
    const struct aws_string * str_b = b;
    return str_a->len == str_b->len && !memcmp(aws_string_bytes(str_a),
                                               aws_string_bytes(str_b),
                                               str_a->len);
}

bool aws_ptr_eq(const void *a, const void *b) {
    return a == b;
}
