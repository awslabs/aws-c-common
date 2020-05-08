/*
 * Copyright 2010-2020 Amazon.com, Inc. or its affiliates. All Rights Reserved.
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
#include <aws/common/lifo_cache.h>

int aws_lifo_cache_init(
    struct aws_lifo_cache *cache,
    struct aws_allocator *allocator,
    aws_hash_fn *hash_fn,
    aws_hash_callback_eq_fn *equals_fn,
    aws_hash_callback_destroy_fn *destroy_key_fn,
    aws_hash_callback_destroy_fn *destroy_value_fn,
    size_t max_items) {
    AWS_ASSERT(allocator);
    AWS_ASSERT(max_items);

    cache->max_items = max_items;

    return aws_linked_hash_table_init(
        &cache->table, allocator, hash_fn, equals_fn, destroy_key_fn, destroy_value_fn, max_items);
}

void aws_lifo_cache_clean_up(struct aws_lifo_cache *cache) {
    /* clearing the table will remove all elements. That will also deallocate
     * any cache entries we currently have. */
    aws_linked_hash_table_clean_up(&cache->table);
    AWS_ZERO_STRUCT(*cache);
}

int aws_lifo_cache_find(struct aws_lifo_cache *cache, const void *key, void **p_value) {

    return (aws_linked_hash_table_find(&cache->table, key, p_value));
}

int aws_lifo_cache_put(struct aws_lifo_cache *cache, const void *key, void *p_value) {

    if (aws_linked_hash_table_put(&cache->table, key, p_value)) {
        return AWS_OP_ERR;
    }

    /* Manage the space if we actually added a new element and the cache is full. */
    if (aws_linked_hash_table_get_element_count(&cache->table) > cache->max_items) {
        /* we're over the cache size limit. Remove whatever is in the one before the back of the linked_hash_table,
         * which was the latest element before we put the new one */
        const struct aws_linked_list *list = aws_linked_hash_table_get_iteration_list(&cache->table);
        struct aws_linked_list_node *node = aws_linked_list_back(list);
        if (!node->prev) {
            return AWS_OP_SUCCESS;
        }
        struct aws_linked_hash_table_node *table_node =
            AWS_CONTAINER_OF(node->prev, struct aws_linked_hash_table_node, node);
        return aws_linked_hash_table_remove(&cache->table, table_node->key);
    }

    return AWS_OP_SUCCESS;
}

int aws_lifo_cache_remove(struct aws_lifo_cache *cache, const void *key) {
    /* allocated cache memory and the linked list entry will be removed in the
     * callback. */
    return aws_linked_hash_table_remove(&cache->table, key);
}

void aws_lifo_cache_clear(struct aws_lifo_cache *cache) {
    /* clearing the table will remove all elements. That will also deallocate
     * any cache entries we currently have. */
    aws_linked_hash_table_clear(&cache->table);
}

size_t aws_lifo_cache_get_element_count(const struct aws_lifo_cache *cache) {
    return aws_linked_hash_table_get_element_count(&cache->table);
}
