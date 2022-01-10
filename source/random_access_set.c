
/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/common/allocator.h>
#include <aws/common/device_random.h>
#include <aws/common/random_access_set.h>

struct aws_random_access_set_impl {
    struct aws_allocator *allocator;
    struct aws_array_list list;
    struct aws_hash_table map; /* map from the element to the index in the array */
    aws_hash_callback_destroy_fn *destroy_element_fn;
};

static void s_impl_destroy(struct aws_random_access_set_impl *impl) {
    if (!impl) {
        return;
    }
    aws_array_list_clean_up(&impl->list);
    aws_hash_table_clean_up(&impl->map);
    aws_mem_release(impl->allocator, impl);
}

static struct aws_random_access_set_impl *s_impl_new(
    struct aws_allocator *allocator,
    aws_hash_fn *hash_fn,
    aws_hash_callback_eq_fn *equals_fn,
    aws_hash_callback_destroy_fn *destroy_element_fn,
    size_t initial_item_allocation) {
    struct aws_random_access_set_impl *impl = aws_mem_calloc(allocator, 1, sizeof(struct aws_random_access_set_impl));
    impl->allocator = allocator;

    if (aws_array_list_init_dynamic(&impl->list, allocator, initial_item_allocation, sizeof(void *))) {
        s_impl_destroy(impl);
        return NULL;
    }

    if (aws_hash_table_init(
            &impl->map, allocator, initial_item_allocation, hash_fn, equals_fn, destroy_element_fn, NULL)) {
        s_impl_destroy(impl);
        return NULL;
    }
    impl->destroy_element_fn = destroy_element_fn;
    return impl;
}

int aws_random_access_set_init(
    struct aws_random_access_set *set,
    struct aws_allocator *allocator,
    aws_hash_fn *hash_fn,
    aws_hash_callback_eq_fn *equals_fn,
    aws_hash_callback_destroy_fn *destroy_element_fn,
    size_t initial_item_allocation) {
    struct aws_random_access_set_impl *impl =
        s_impl_new(allocator, hash_fn, equals_fn, destroy_element_fn, initial_item_allocation);
    if (!impl) {
        return AWS_OP_ERR;
    }
    set->impl = impl;
    return AWS_OP_SUCCESS;
}

void aws_random_access_set_clean_up(struct aws_random_access_set *set) {
    if (!set) {
        return;
    }
    s_impl_destroy(set->impl);
}

int aws_random_access_set_insert(struct aws_random_access_set *set, const void *element) {
    AWS_PRECONDITION(set);
    AWS_PRECONDITION(element);
    if (aws_random_access_set_exist(set, element)) {
        return aws_raise_error(AWS_ERROR_INVALID_ARGUMENT /*TODO: some more specific error or not?*/);
    }
    if (aws_array_list_push_back(&set->impl->list, (void *)&element)) {
        goto list_push_error;
    }
    if (aws_hash_table_put(&set->impl->map, element, (void *)(aws_array_list_length(&set->impl->list) - 1), NULL)) {
        goto error;
    }
    return AWS_OP_SUCCESS;
error:
    aws_array_list_pop_back(&set->impl->list);
list_push_error:
    return AWS_OP_ERR;
}

int aws_random_access_set_remove(struct aws_random_access_set *set, const void *element) {
    AWS_PRECONDITION(set);
    AWS_PRECONDITION(element);
    size_t current_length = aws_array_list_length(&set->impl->list);
    if (current_length == 0) {
        /* Nothing to remove */
        return AWS_OP_SUCCESS;
    }
    struct aws_hash_element *find = NULL;
    /* find and remove the element from table */
    if (aws_hash_table_find(&set->impl->map, element, &find)) {
        return AWS_OP_ERR;
    }
    if (!find) {
        /* It's removed already */
        return AWS_OP_SUCCESS;
    }

    size_t index_to_remove = (size_t)find->value;
    if (aws_hash_table_remove_element(&set->impl->map, find)) {
        return AWS_OP_ERR;
    }
    /* Nothing else can fail after here. */
    if (index_to_remove != current_length - 1) {
        /* It's not the last element, we need to swap it with the end of the list and remove the last element */
        void *last_element = NULL;
        AWS_FATAL_ASSERT(
            aws_array_list_get_at_ptr(&set->impl->list, &last_element, current_length - 1) == AWS_OP_SUCCESS);
        /* Update the last element index in the table */
        struct aws_hash_element *element_to_update = NULL;
        AWS_FATAL_ASSERT(
            aws_hash_table_find(&set->impl->map, *(void **)last_element, &element_to_update) == AWS_OP_SUCCESS);
        AWS_FATAL_ASSERT(element_to_update != NULL);
        element_to_update->value = (void *)index_to_remove;
        /* Swap the last element with the element to remove in the list */
        aws_array_list_swap(&set->impl->list, index_to_remove, current_length - 1);
    }
    /* Remove the current last element from the list */
    AWS_FATAL_ASSERT(aws_array_list_pop_back(&set->impl->list) == AWS_OP_SUCCESS);
    if (set->impl->destroy_element_fn) {
        set->impl->destroy_element_fn((void *)element);
    }
    return AWS_OP_SUCCESS;
}

int aws_random_access_set_get_random(struct aws_random_access_set *set, void *out) {
    AWS_PRECONDITION(set);
    size_t length = aws_array_list_length(&set->impl->list);
    if (length == 0) {
        return aws_raise_error(AWS_ERROR_LIST_EMPTY);
    }

    uint64_t random_64_bit_num = 0;
    aws_device_random_u64(&random_64_bit_num);

    size_t index = (size_t)random_64_bit_num % length;
    void *element = NULL;
    AWS_FATAL_ASSERT(aws_array_list_get_at_ptr(&set->impl->list, &element, index) == AWS_OP_SUCCESS);
    memcpy(out, *(void **)element, sizeof(void *));

    return AWS_OP_SUCCESS;
}

size_t aws_random_access_set_get_size(struct aws_random_access_set *set) {
    return aws_array_list_length(&set->impl->list);
}

bool aws_random_access_set_exist(struct aws_random_access_set *set, const void *element) {
    struct aws_hash_element *find = NULL;
    AWS_FATAL_ASSERT(aws_hash_table_find(&set->impl->map, element, &find) == AWS_OP_SUCCESS);
    return find != NULL;
}
