/*
 * Copyright 2010-2018 Amazon.com, Inc. or its affiliates. All Rights Reserved.
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

/* This is implicitly included, but helps with editor highlighting */
#include <aws/common/array_list.h>
/*
 * Do not add system headers here; add them to array_list.h. This file is included under extern "C" guards,
 * which might break system headers.
 */

AWS_STATIC_IMPL
int aws_array_list_init_dynamic(
    struct aws_array_list *AWS_RESTRICT list,
    struct aws_allocator *alloc,
    size_t initial_item_allocation,
    size_t item_size) {
    if (item_size == 0) {
        return aws_raise_error(AWS_ERROR_INVALID_ARGUMENT);
    }

    list->alloc = alloc;
    size_t allocation_size;
    if (aws_mul_size_checked(initial_item_allocation, item_size, &allocation_size)) {
        return AWS_OP_ERR;
    }
    list->data = NULL;
    list->item_size = item_size;
    list->current_size = 0;
    list->length = 0;

    if (allocation_size > 0) {
        list->data = aws_mem_acquire(list->alloc, allocation_size);
        if (!list->data) {
            return AWS_OP_ERR;
        }
#ifdef DEBUG_BUILD
        memset(list->data, AWS_ARRAY_LIST_DEBUG_FILL, allocation_size);
#endif
        list->current_size = allocation_size;
    }
    AWS_FATAL_ASSERT(list->current_size == 0 || list->data);

    return AWS_OP_SUCCESS;
}

AWS_STATIC_IMPL
void aws_array_list_init_static(
    struct aws_array_list *AWS_RESTRICT list,
    void *raw_array,
    size_t item_count,
    size_t item_size) {
    AWS_FATAL_ASSERT(raw_array);
    AWS_FATAL_ASSERT(item_count);
    AWS_FATAL_ASSERT(item_size);

    list->alloc = NULL;

    int no_overflow = !aws_mul_size_checked(item_count, item_size, &list->current_size);
    AWS_FATAL_ASSERT(no_overflow);

    list->item_size = item_size;
    list->length = 0;
    list->data = raw_array;
}

AWS_STATIC_IMPL
void aws_array_list_clean_up(struct aws_array_list *AWS_RESTRICT list) {
    if (list->alloc && list->data) {
        aws_mem_release(list->alloc, list->data);
    }

    list->current_size = 0;
    list->item_size = 0;
    list->length = 0;
    list->data = NULL;
    list->alloc = NULL;
}

AWS_STATIC_IMPL
int aws_array_list_push_back(struct aws_array_list *AWS_RESTRICT list, const void *val) {
    int err_code = aws_array_list_set_at(list, val, aws_array_list_length(list));

    if (err_code && aws_last_error() == AWS_ERROR_INVALID_INDEX && !list->alloc) {
        return aws_raise_error(AWS_ERROR_LIST_EXCEEDS_MAX_SIZE);
    }

    return err_code;
}

AWS_STATIC_IMPL
int aws_array_list_front(const struct aws_array_list *AWS_RESTRICT list, void *val) {
    if (aws_array_list_length(list) > 0) {
        memcpy(val, list->data, list->item_size);
        return AWS_OP_SUCCESS;
    }

    return aws_raise_error(AWS_ERROR_LIST_EMPTY);
}

AWS_STATIC_IMPL
int aws_array_list_pop_front(struct aws_array_list *AWS_RESTRICT list) {
    if (aws_array_list_length(list) > 0) {
        aws_array_list_pop_front_n(list, 1);
        return AWS_OP_SUCCESS;
    }

    return aws_raise_error(AWS_ERROR_LIST_EMPTY);
}

AWS_STATIC_IMPL
void aws_array_list_pop_front_n(struct aws_array_list *AWS_RESTRICT list, size_t n) {
    if (n >= aws_array_list_length(list)) {
        aws_array_list_clear(list);
        return;
    }

    if (n > 0) {
        size_t popping_bytes = list->item_size * n;
        size_t remaining_items = aws_array_list_length(list) - n;
        size_t remaining_bytes = remaining_items * list->item_size;
        memmove(list->data, (uint8_t *)list->data + popping_bytes, remaining_bytes);
        list->length = remaining_items;
#ifdef DEBUG_BUILD
        memset((uint8_t *)list->data + remaining_bytes, AWS_ARRAY_LIST_DEBUG_FILL, popping_bytes);
#endif
    }
}

AWS_STATIC_IMPL
int aws_array_list_back(const struct aws_array_list *AWS_RESTRICT list, void *val) {
    if (aws_array_list_length(list) > 0) {
        size_t last_item_offset = list->item_size * (aws_array_list_length(list) - 1);

        memcpy(val, (void *)((uint8_t *)list->data + last_item_offset), list->item_size);
        return AWS_OP_SUCCESS;
    }

    return aws_raise_error(AWS_ERROR_LIST_EMPTY);
}

AWS_STATIC_IMPL
int aws_array_list_pop_back(struct aws_array_list *AWS_RESTRICT list) {
    if (aws_array_list_length(list) > 0) {

        AWS_FATAL_ASSERT(list->data);

        size_t last_item_offset = list->item_size * (aws_array_list_length(list) - 1);

        memset((void *)((uint8_t *)list->data + last_item_offset), 0, list->item_size);
        list->length--;
        return AWS_OP_SUCCESS;
    }

    return aws_raise_error(AWS_ERROR_LIST_EMPTY);
}

AWS_STATIC_IMPL
void aws_array_list_clear(struct aws_array_list *AWS_RESTRICT list) {
    if (list->data) {
#ifdef DEBUG_BUILD
        memset(list->data, AWS_ARRAY_LIST_DEBUG_FILL, list->current_size);
#endif
        list->length = 0;
    }
}

AWS_STATIC_IMPL
void aws_array_list_swap_contents(
    struct aws_array_list *AWS_RESTRICT list_a,
    struct aws_array_list *AWS_RESTRICT list_b) {
    AWS_FATAL_ASSERT(list_a->alloc);
    AWS_FATAL_ASSERT(list_a->alloc == list_b->alloc);
    AWS_FATAL_ASSERT(list_a->item_size == list_b->item_size);
    AWS_FATAL_ASSERT(list_a != list_b);

    struct aws_array_list tmp = *list_a;
    *list_a = *list_b;
    *list_b = tmp;
}

AWS_STATIC_IMPL
size_t aws_array_list_capacity(const struct aws_array_list *AWS_RESTRICT list) {
    AWS_FATAL_ASSERT(list->item_size);
    return list->current_size / list->item_size;
}

AWS_STATIC_IMPL
size_t aws_array_list_length(const struct aws_array_list *AWS_RESTRICT list) {
    /*
     * This assert teaches clang-tidy and friends that list->data cannot be null in a non-empty
     * list.
     */
    AWS_FATAL_ASSERT(!list->length || list->data);

    return list->length;
}

AWS_STATIC_IMPL
int aws_array_list_get_at(const struct aws_array_list *AWS_RESTRICT list, void *val, size_t index) {
    if (aws_array_list_length(list) > index) {
        memcpy(val, (void *)((uint8_t *)list->data + (list->item_size * index)), list->item_size);
        return AWS_OP_SUCCESS;
    }
    return aws_raise_error(AWS_ERROR_INVALID_INDEX);
}

AWS_STATIC_IMPL
int aws_array_list_get_at_ptr(const struct aws_array_list *AWS_RESTRICT list, void **val, size_t index) {
    if (aws_array_list_length(list) > index) {
        *val = (void *)((uint8_t *)list->data + (list->item_size * index));
        return AWS_OP_SUCCESS;
    }
    return aws_raise_error(AWS_ERROR_INVALID_INDEX);
}

AWS_STATIC_IMPL
int aws_array_list_calc_necessary_size(struct aws_array_list *AWS_RESTRICT list, size_t index, size_t *necessary_size) {
    size_t index_inc;
    if (aws_add_size_checked(index, 1, &index_inc)) {
        return AWS_OP_ERR;
    }

    if (aws_mul_size_checked(index_inc, list->item_size, necessary_size)) {
        return AWS_OP_ERR;
    }
    return AWS_OP_SUCCESS;
}

AWS_STATIC_IMPL
int aws_array_list_set_at(struct aws_array_list *AWS_RESTRICT list, const void *val, size_t index) {
    size_t necessary_size;
    if (aws_array_list_calc_necessary_size(list, index, &necessary_size)) {
        return AWS_OP_ERR;
    }

    if (list->current_size < necessary_size) {
        if (aws_array_list_ensure_capacity(list, index)) {
            return AWS_OP_ERR;
        }
    }

    AWS_FATAL_ASSERT(list->data);

    memcpy((void *)((uint8_t *)list->data + (list->item_size * index)), val, list->item_size);

    /*
     * This isn't perfect, but its the best I can come up with for detecting
     * length changes.
     */
    if (index >= aws_array_list_length(list)) {
        if (aws_add_size_checked(index, 1, &list->length)) {
            return AWS_OP_ERR;
        }
    }

    return AWS_OP_SUCCESS;
}

AWS_STATIC_IMPL
void aws_array_list_sort(struct aws_array_list *AWS_RESTRICT list, aws_array_list_comparator_fn *compare_fn) {
    if (list->data) {
        qsort(list->data, aws_array_list_length(list), list->item_size, compare_fn);
    }
}
