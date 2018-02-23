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

#include <aws/common/array_list.h>
#include <assert.h>

#define SENTINAL 0xDD

int aws_array_list_init_dynamic(struct aws_array_list *list, struct aws_allocator *alloc,
                                size_t initial_item_allocation, size_t item_size) {
    list->alloc = alloc;
    size_t allocation_size = initial_item_allocation * item_size;
    list->data = NULL;
    list->item_size = item_size;

    if (allocation_size > 0) {
        list->data = aws_mem_acquire(list->alloc, allocation_size);
        list->length = 0;
        if (!list->data) {
            return aws_raise_error(AWS_ERROR_OOM);
        }
#ifdef DEBUG_BUILD
        memset(list->data, SENTINAL, allocation_size);
#endif
        list->current_size = allocation_size;
    }

    return AWS_OP_SUCCESS;
}

int aws_array_list_init_static(struct aws_array_list *list, void *raw_array, size_t item_count, size_t item_size) {
    assert(raw_array);
    assert(item_count);
    assert(item_size);

    list->alloc = NULL;

    list->current_size = item_count * item_size;
    list->item_size = item_size;
    list->length = 0;
    list->data = raw_array;
    return AWS_OP_SUCCESS;
}

void aws_array_list_clean_up(struct aws_array_list *list) {
    if (list->alloc && list->data) {
        aws_mem_release(list->alloc, list->data);
    }

    list->current_size = 0;
    list->item_size = 0;
    list->length = 0;
    list->data = NULL;
    list->alloc = NULL;
}

int aws_array_list_push_back(struct aws_array_list *list, const void *val) {
    int err_code = aws_array_list_set_at(list, val, list->length);

    if (err_code && aws_last_error() == AWS_ERROR_INVALID_INDEX && !list->alloc) {
        return aws_raise_error(AWS_ERROR_LIST_EXCEEDS_MAX_SIZE);
    }

    return err_code;
}

int aws_array_list_front(const struct aws_array_list *list, void *val) {

    if (list->length > 0) {
        memcpy(val, list->data, list->item_size);
        return AWS_OP_SUCCESS;
    }

    return aws_raise_error(AWS_ERROR_LIST_EMPTY);
}

int aws_array_list_pop_front(struct aws_array_list *list) {
    if (list->length > 0) {
        size_t last_bytes = list->item_size * (list->length - 1);
        memmove(list->data, (void *)((uint8_t *)list->data + list->item_size), last_bytes);
#ifdef DEBUG_BUILD
        memset((void *)((uint8_t *)list->data + last_bytes), SENTINAL, list->item_size);
#endif
        list->length--;
        return AWS_OP_SUCCESS;
    }

    return aws_raise_error(AWS_ERROR_LIST_EMPTY);
}

int aws_array_list_back(const struct aws_array_list *list, void *val) {
    if (list->length > 0) {
        size_t last_item_offset = list->item_size * (list->length - 1);

        memcpy(val, (void *)((uint8_t *)list->data + last_item_offset), list->item_size);
        return AWS_OP_SUCCESS;
    }

    return aws_raise_error(AWS_ERROR_LIST_EMPTY);
}

int aws_array_list_pop_back(struct aws_array_list *list) {
    if (list->length > 0) {
        size_t last_item_offset = list->item_size * (list->length - 1);

        memset((void *)((uint8_t *)list->data + last_item_offset), 0, list->item_size);
        list->length--;
        return AWS_OP_SUCCESS;
    }

    return aws_raise_error(AWS_ERROR_LIST_EMPTY);
}

void aws_array_list_clear(struct aws_array_list *list) {
    if (list->length > 0) {
#ifdef DEBUG_BUILD
        memset(list->data, SENTINAL, list->current_size);
#endif
        list->length = 0;
    }
}

int aws_array_list_shrink_to_fit(struct aws_array_list *list) {
    if (list->alloc) {
        size_t ideal_size = list->length * list->item_size;
        if (ideal_size < list->current_size) {
            void *raw_data = aws_mem_acquire(list->alloc, ideal_size);
            if (!raw_data) {
                return aws_raise_error(AWS_ERROR_OOM);
            }

            memcpy(raw_data, list->data, ideal_size);
            aws_mem_release(list->alloc, list->data);
            list->data = raw_data;
            list->current_size = ideal_size;
        }
        return AWS_OP_SUCCESS;
    }

    return aws_raise_error(AWS_ERROR_LIST_STATIC_MODE_CANT_SHRINK);
}

int aws_array_list_copy(const struct aws_array_list *from, struct aws_array_list *to) {
    assert(from->item_size == to->item_size);

    size_t copy_size = from->length * from->item_size;

    if (to->length >= from->length) {
        memcpy(to->data, from->data, copy_size);
        to->length = from->length;
        return AWS_OP_SUCCESS;
    }
    /* if to is in dynamic mode, we can just reallocate it and copy */
    else if (to->alloc != NULL) {
        void *tmp = aws_mem_acquire(to->alloc, copy_size);

        if (!tmp) {
            return aws_raise_error(AWS_ERROR_OOM);
        }

        memcpy(tmp, from->data, copy_size);
        if (to->data) {
            aws_mem_release(to->alloc, to->data);
        }

        to->data = tmp;
        to->length = from->length;
        to->current_size = copy_size;
        return AWS_OP_SUCCESS;
    }

    return aws_raise_error(AWS_ERROR_LIST_DEST_COPY_TOO_SMALL);
}

size_t aws_array_list_capacity(const struct aws_array_list *list) {
    assert(list->item_size);
    return list->current_size / list->item_size;
}

size_t aws_array_list_length(const struct aws_array_list *list) {
    return list->length;
}

int aws_array_list_get_at(const struct aws_array_list *list, void *val, size_t index) {
    if (list->length > index) {
        memcpy(val, (void *)((uint8_t *)list->data + (list->item_size * index)), list->item_size);
        return AWS_OP_SUCCESS;
    }
    return aws_raise_error(AWS_ERROR_INVALID_INDEX);
}

int aws_array_list_get_at_ptr(const struct aws_array_list *list, void **val, size_t index) {

    if (list->length > index) {
        *val = (void *)((uint8_t *)list->data + (list->item_size * index));
        return AWS_OP_SUCCESS;
    }
    return aws_raise_error(AWS_ERROR_INVALID_INDEX);
}

int aws_array_list_set_at(struct aws_array_list *list, const void *val, size_t index) {
    size_t necessary_size = index * list->item_size;

    if (list->current_size <= necessary_size) {
        if (!list->alloc) {
            return aws_raise_error(AWS_ERROR_INVALID_INDEX);
        }

        /* this will double capacity if the index isn't bigger than what the next allocation would be,
         * but allocates the exact requested size if it is. This is largely because we don't have a
         * good way to predict the usage pattern to make a smart decision about it. However, if the user
         * is doing this in an iterative fashion, necessary_size will never be used.*/
        size_t next_allocation_size = list->current_size << 1;
        size_t new_size = 0;
        AWS_MAX(necessary_size, next_allocation_size, new_size);

        if (new_size < list->current_size) {
            /* this means new_size overflowed. The only way this happens is on a 32-bit system
             * where size_t is 32 bits, in which case we're out of addressable memory anyways, or
             * we're on a 64 bit system and we're most certainly out of addressable memory.
             * But since we're simply going to fail fast and say, sorry can't do it, we'll just tell
             * the user they can't grow the list anymore. */
            return aws_raise_error(AWS_ERROR_LIST_EXCEEDS_MAX_SIZE);
        }

        void *temp = aws_mem_acquire(list->alloc, new_size);

        if (!temp) {
            return aws_raise_error(AWS_ERROR_OOM);
        }

        memcpy(temp, list->data, list->current_size);

#ifdef DEBUG_BUILD
        memset((void *)((uint8_t *)temp + list->current_size), SENTINAL, new_size - list->current_size);
#endif
        aws_mem_release(list->alloc, list->data);
        list->data = temp;
        list->current_size = new_size;
    }

    memcpy((void *)((uint8_t *)list->data + (list->item_size * index)), val, list->item_size);

    /* this isn't perfect but its the best I can come up with for detecting length changes*/
    if (index >= list->length) {
        list->length = index + 1;
    }

    return AWS_OP_SUCCESS;
}

void aws_array_list_mem_swap(void *AWS_RESTRICT item1, void *AWS_RESTRICT item2, size_t item_size) {
    enum { SLICE = 128 };

    /* copy SLICE sized bytes at a time */
    size_t slice_count = item_size / SLICE;
    uint8_t temp[SLICE];
    for (size_t i = 0; i < slice_count; i++) {
        memcpy((void *)temp, (void *)item1, SLICE);
        memcpy((void *)item1, (void *)item2, SLICE);
        memcpy((void *)item2, (void *)temp, SLICE);
        item1 = (uint8_t *)item1 + SLICE;
        item2 = (uint8_t *)item2 + SLICE;
    }

    size_t remainder = item_size & (SLICE - 1); /* item_size % SLICE */
    memcpy((void *)temp, (void *)item1, remainder);
    memcpy((void *)item1, (void *)item2, remainder);
    memcpy((void *)item2, (void *)temp, remainder);
}

void aws_array_list_swap(struct aws_array_list *list, size_t a, size_t b) {
    assert(a < list->length);
    assert(b < list->length);
    if (a == b) {
        return;
    }

    void *item1, *item2;
    aws_array_list_get_at_ptr(list, &item1, a);
    aws_array_list_get_at_ptr(list, &item2, b);
    aws_array_list_mem_swap(item1, item2, list->item_size);
}
