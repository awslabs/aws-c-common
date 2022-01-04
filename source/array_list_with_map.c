
/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/common/allocator.h>
#include <aws/common/array_list_with_map.h>
#include <aws/common/device_random.h>
#include <aws/common/string.h>

int aws_array_list_with_map_init(
    struct aws_array_list_with_map *list_with_map,
    struct aws_allocator *allocator,
    aws_hash_fn *hash_fn,
    aws_hash_callback_eq_fn *equals_fn,
    aws_hash_callback_destroy_fn *destroy_element_fn,
    size_t item_size,
    size_t initial_item_allocation) {
    if (aws_array_list_init_dynamic(&list_with_map->list, allocator, initial_item_allocation, item_size)) {
        return AWS_OP_ERR;
    }

    if (aws_hash_table_init(
            &list_with_map->map, allocator, initial_item_allocation, hash_fn, equals_fn, destroy_element_fn, NULL)) {
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
    if (aws_array_list_with_map_exist(list_with_map, element)) {
        return aws_raise_error(AWS_ERROR_INVALID_ARGUMENT /*TODO: some more specific error or not?*/);
    }
    size_t current_length = aws_array_list_length(&list_with_map->list);
    if (aws_array_list_push_back(&list_with_map->list, element)) {
        goto list_push_error;
    }
    if (aws_hash_table_put(&list_with_map->map, element, (void *)current_length, NULL)) {
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

    struct aws_hash_element *find = NULL;
    /* find and remove the elment from table */
    if (aws_hash_table_find(&list_with_map->map, element, &find)) {
        return AWS_OP_ERR;
    }
    if (!find) {
        /* It's removed already */
        return AWS_OP_SUCCESS;
    }

    size_t index_to_remove = (size_t)find->value;
    if (aws_hash_table_remove(&list_with_map->map, element, NULL, NULL)) {
        return AWS_OP_ERR;
    }
    /* Nothing else can fail after here. */

    if (index_to_remove != current_length - 1) {
        /* It's not the last element, we need to swap it with the end of the list and remove the last element */
        void *last_element = aws_mem_acquire(list_with_map->list.alloc, list_with_map->list.item_size);
        AWS_FATAL_ASSERT(aws_array_list_back(&list_with_map->list, last_element) == AWS_OP_SUCCESS);
        /* Update the last element index in the table */
        struct aws_hash_element *element_to_update = NULL;
        AWS_FATAL_ASSERT(aws_hash_table_find(&list_with_map->map, last_element, &element_to_update) == AWS_OP_SUCCESS);
        AWS_FATAL_ASSERT(element_to_update != NULL);
        element_to_update->value = (void *)index_to_remove;
        /* Swap the last element with the element to remove in the list */
        aws_array_list_swap(&list_with_map->list, index_to_remove, current_length - 1);
        aws_mem_release(list_with_map->list.alloc, last_element);
    }
    /* Remove the current last element from the list */
    AWS_FATAL_ASSERT(aws_array_list_pop_back(&list_with_map->list) == AWS_OP_SUCCESS);
    return AWS_OP_SUCCESS;
}

int aws_array_list_with_map_get_random(struct aws_array_list_with_map *list_with_map, void *out) {
    AWS_PRECONDITION(list_with_map);
    size_t length = aws_array_list_length(&list_with_map->list);
    if (length == 0) {
        return aws_raise_error(AWS_ERROR_LIST_EMPTY);
    }

    /* use the best of two algorithm to select the connection with the lowest load. */
    uint64_t random_64_bit_num = 0;
    aws_device_random_u64(&random_64_bit_num);
    size_t index = random_64_bit_num % length;
    AWS_FATAL_ASSERT(aws_array_list_get_at(&list_with_map->list, out, index) == AWS_OP_SUCCESS);
    return AWS_OP_SUCCESS;
}

size_t aws_array_list_with_map_length(struct aws_array_list_with_map *list_with_map) {
    return aws_array_list_length(&list_with_map->list);
}

bool aws_array_list_with_map_exist(struct aws_array_list_with_map *list_with_map, const void *element) {
    struct aws_hash_element *find = NULL;
    AWS_FATAL_ASSERT(aws_hash_table_find(&list_with_map->map, element, &find) == AWS_OP_SUCCESS);
    return find != NULL;
}
