#ifndef AWS_COMMON_PRIVATE_HASH_TABLE_IMPL_H
#define AWS_COMMON_PRIVATE_HASH_TABLE_IMPL_H

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

#include <aws/common/common.h>
#include <aws/common/hash_table.h>
#include <aws/common/math.h>

struct hash_table_entry {
    struct aws_hash_element element;
    uint64_t hash_code; /* hash code (0 signals empty) */
};

/* Using a flexible array member is the C99 compliant way to have the hash_table_entries
 * immediatly follow the struct.
 *
 * MSVC doesn't know this for some reason so we need to use a pragma to make
 * it happy.
 */
#ifdef _MSC_VER
#    pragma warning(push)
#    pragma warning(disable : 4200)
#endif
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
    struct hash_table_entry slots[];
};
#ifdef _MSC_VER
#    pragma warning(pop)
#endif

/**
 * Best-effort check of hash_table_state data-structure invarients
 * Some invarients, such as that the number of entries is actually the
 * same as the entry_count field, would require a loop to check
 */
AWS_STATIC_IMPL
bool hash_table_state_is_valid(const struct hash_table_state *map) {
    if (!map) {
        return false;
    }
    bool hash_fn_nonnull = (map->hash_fn != NULL);
    bool equals_fn_nonnull = (map->equals_fn != NULL);
    /*destroy_key_fn and destroy_value_fn are both allowed to be NULL*/
    bool alloc_nonnull = (map->alloc != NULL);
    bool size_at_least_two = (map->size >= 2);
    bool size_is_power_of_two = aws_is_power_of_two(map->size);
    bool entry_count = (map->entry_count <= map->max_load);
    bool max_load = (map->max_load < map->size);
    bool mask_is_correct = (map->mask == (map->size - 1));
    bool max_load_factor_bounded = map->max_load_factor == 0.95; //(map->max_load_factor < 1.0);
    bool slots_allocated = AWS_MEM_IS_WRITABLE(&map->slots[0], sizeof(map->slots[0]) * map->size);

    return hash_fn_nonnull && equals_fn_nonnull && alloc_nonnull && size_at_least_two && size_is_power_of_two &&
           entry_count && max_load && mask_is_correct && max_load_factor_bounded && slots_allocated;
}

/**
 * Best-effort check of hash_table_state data-structure invarients
 * Some invarients, such as that the number of entries is actually the
 * same as the entry_count field, would require a loop to check
 */
AWS_STATIC_IMPL
bool aws_hash_table_is_valid(const struct aws_hash_table *map) {
    return map && map->p_impl && hash_table_state_is_valid(map->p_impl);
}

/**
 * Given a pointer to a hash_iter, checks that it is well-formed, with all data-structure invariants.
 */
AWS_STATIC_IMPL
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
    if (iter->limit > iter->map->p_impl->size) {
        return false;
    }

    switch (iter->status) {
        case AWS_HASH_ITER_STATUS_DONE:
            /* Done iff slot == limit */
            return iter->slot == iter->limit;
        case AWS_HASH_ITER_STATUS_DELETE_CALLED:
            /* iter->slot can underflow to SIZE_MAX after a delete
             * see the comments for aws_hash_iter_delete() */
            return iter->slot <= iter->limit || iter->slot == SIZE_MAX;
        case AWS_HASH_ITER_STATUS_READY_FOR_USE:
            /* A slot must point to a valid location (i.e. hash_code != 0) */
            return iter->slot < iter->limit && iter->map->p_impl->slots[iter->slot].hash_code != 0;
    }
    /* Invalid status code */
    return false;
}

/**
 * Determine the total number of bytes needed for a hash-table with
 * "size" slots. If the result would overflow a size_t, return
 * AWS_OP_ERR; otherwise, return AWS_OP_SUCCESS with the result in
 * "required_bytes".
 */
AWS_STATIC_IMPL
int hash_table_state_required_bytes(size_t size, size_t *required_bytes) {

    size_t elemsize;
    if (aws_mul_size_checked(size, sizeof(struct hash_table_entry), &elemsize)) {
        return AWS_OP_ERR;
    }

    if (aws_add_size_checked(elemsize, sizeof(struct hash_table_state), required_bytes)) {
        return AWS_OP_ERR;
    }

    return AWS_OP_SUCCESS;
}

#endif /* AWS_COMMON_PRIVATE_HASH_TABLE_IMPL_H */
