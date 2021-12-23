
/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/common/allocator.h>
#include <aws/common/array_list_with_map.h>
#include <aws/common/device_random.h>

int aws_array_list_with_map_init(
    struct aws_array_list_with_map *list_with_map,
    struct aws_allocator *allocator,
    aws_hash_fn *hash_fn,
    aws_hash_callback_eq_fn *equals_fn,
    size_t item_size,
    size_t initial_item_allocation) {
    if (aws_array_list_init_dynamic(&list_with_map->list, allocator, initial_item_allocation, item_size)) {
        return AWS_OP_ERR;
    }
    /* Array list owns the element, so, no need to destroy the key. */
    if (aws_hash_table_init(&list_with_map->map, allocator, initial_item_allocation, hash_fn, equals_fn, NULL, NULL)) {
        aws_array_list_clean_up(&list_with_map->list);
        return AWS_OP_ERR;
    }
    return AWS_OP_SUCCESS;
}

void aws_array_list_with_map_clean_up(struct aws_array_list_with_map *list_with_map) {
    if (!list_with_map) {
        return;
    }
    aws_array_list_clean_up(&list_with_map->list);
    aws_hash_table_clean_up(&list_with_map->map);
}

int aws_array_list_with_map_insert(struct aws_array_list_with_map *list_with_map, const void *element) {
    AWS_PRECONDITION(list_with_map);
    AWS_PRECONDITION(element);
    size_t current_length = aws_array_list_length(&list_with_map->list);
    int was_created = 0;
    if (aws_array_list_push_back(&list_with_map->list, element)) {
        goto list_push_error;
    }
    if (aws_hash_table_put(&list_with_map->map, element, (void *)current_length, &was_created)) {
        goto error;
    }
    if (!was_created) {
        /* We have duplicate that we don't support */
        aws_raise_error(AWS_ERROR_INVALID_ARGUMENT /*TODO: some more specific error or not?*/);
        goto error;
    }
    return AWS_OP_SUCCESS;
error:
    aws_array_list_pop_back(&list_with_map->list);
list_push_error:
    return AWS_OP_ERR;
}

int aws_array_list_with_map_remove(struct aws_array_list_with_map *list_with_map, const void *element) {
    AWS_PRECONDITION(list_with_map);
    AWS_PRECONDITION(element);
    size_t current_length = aws_array_list_length(&list_with_map->list);
    if (current_length == 0) {
        /* Nothing to remove */
        return AWS_OP_SUCCESS;
    }
    /* find the index of element first */

    struct aws_hash_element found;
    int was_present = 0;
    /* find and remove the elment from table */
    if (aws_hash_table_remove(&list_with_map->map, element, &found, &was_present)) {
        return AWS_OP_ERR;
    }
    if (!was_present) {
        /* It's removed already */
        return AWS_OP_SUCCESS;
    }

    /* Nothing else can fail after here. */
    size_t index_to_remove = (size_t)found.value;
    if (index_to_remove != current_length - 1) {
        /* It's not the last element, we need to swap it with the end of the list and remove the last element */
        void *last_element = aws_mem_acquire(list_with_map->list.alloc, list_with_map->list.item_size);
        AWS_ASSERT(aws_array_list_back(&list_with_map->list, last_element) == AWS_OP_SUCCESS);
        /* Update the last element index in the table */
        struct aws_hash_element *element_to_update = NULL;
        AWS_ASSERT(
            aws_hash_table_find(&list_with_map->map, last_element, &element_to_update) == AWS_OP_SUCCESS &&
            element_to_update);
        element_to_update->value = (void *)index_to_remove;
        /* Swap the last element with the element to remove in the list */
        aws_array_list_swap(&list_with_map->list, index_to_remove, current_length - 1);
        aws_mem_release(list_with_map->list.alloc, last_element);
    }
    /* Remove the current last element from the list */
    AWS_ASSERT(aws_array_list_pop_back(&list_with_map->list) == AWS_OP_SUCCESS);
    return AWS_OP_SUCCESS;
}

void aws_array_list_with_map_get_random(struct aws_array_list_with_map *list_with_map, void *out) {
    AWS_PRECONDITION(list_with_map);
    size_t length = aws_array_list_length(&list_with_map->list);
    /* use the best of two algorithm to select the connection with the lowest load. */
    uint64_t random_64_bit_num = 0;
    aws_device_random_u64(&random_64_bit_num);
    AWS_ASSERT(aws_array_list_get_at(&list_with_map->list, out, random_64_bit_num % length) == AWS_OP_SUCCESS);
}

size_t aws_array_list_with_map_length(struct aws_array_list_with_map *list_with_map) {
    return aws_array_list_length(&list_with_map->list);
}

bool aws_array_list_with_map_exist(struct aws_array_list_with_map *list_with_map, const void *element) {
    struct aws_hash_element *find = NULL;
    AWS_ASSERT(aws_hash_table_find(&list_with_map->map, element, &find) == AWS_OP_SUCCESS);
    return find != NULL;
}
