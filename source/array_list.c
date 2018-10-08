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
#include <stdlib.h> /* qsort */

int aws_array_list_shrink_to_fit(struct aws_array_list *AWS_RESTRICT list) {
    if (list->alloc) {
        size_t ideal_size = list->length * list->item_size;
        if (ideal_size < list->current_size) {
            void *raw_data = NULL;

            if (ideal_size > 0) {
                raw_data = aws_mem_acquire(list->alloc, ideal_size);
                if (!raw_data) {
                    return AWS_OP_ERR;
                }

                memcpy(raw_data, list->data, ideal_size);
                aws_mem_release(list->alloc, list->data);
            }
            list->data = raw_data;
            list->current_size = ideal_size;
        }
        return AWS_OP_SUCCESS;
    }

    return aws_raise_error(AWS_ERROR_LIST_STATIC_MODE_CANT_SHRINK);
}

int aws_array_list_copy(const struct aws_array_list *AWS_RESTRICT from, struct aws_array_list *AWS_RESTRICT to) {
    assert(from->item_size == to->item_size);
    assert(from->data);

    size_t copy_size = from->length * from->item_size;

    if (to->current_size >= copy_size) {
        if (copy_size > 0) {
            memcpy(to->data, from->data, copy_size);
        }
        to->length = from->length;
        return AWS_OP_SUCCESS;
    }
    /* if to is in dynamic mode, we can just reallocate it and copy */
    if (to->alloc != NULL) {
        void *tmp = aws_mem_acquire(to->alloc, copy_size);

        if (!tmp) {
            return AWS_OP_ERR;
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

    return aws_raise_error(AWS_ERROR_DEST_COPY_TOO_SMALL);
}

int aws_array_list_ensure_capacity(struct aws_array_list *AWS_RESTRICT list, size_t index) {
    size_t necessary_size = (index + 1) * list->item_size;

    if (list->current_size < necessary_size) {
        if (!list->alloc) {
            return aws_raise_error(AWS_ERROR_INVALID_INDEX);
        }

        /* this will double capacity if the index isn't bigger than what the
         * next allocation would be, but allocates the exact requested size if
         * it is. This is largely because we don't have a good way to predict
         * the usage pattern to make a smart decision about it. However, if the
         * user
         * is doing this in an iterative fashion, necessary_size will never be
         * used.*/
        size_t next_allocation_size = list->current_size << 1;
        size_t new_size = next_allocation_size > necessary_size ? next_allocation_size : necessary_size;

        if (new_size < list->current_size) {
            /* this means new_size overflowed. The only way this happens is on a
             * 32-bit system where size_t is 32 bits, in which case we're out of
             * addressable memory anyways, or we're on a 64 bit system and we're
             * most certainly out of addressable memory. But since we're simply
             * going to fail fast and say, sorry can't do it, we'll just tell
             * the user they can't grow the list anymore. */
            return aws_raise_error(AWS_ERROR_LIST_EXCEEDS_MAX_SIZE);
        }

        void *temp = aws_mem_acquire(list->alloc, new_size);

        if (!temp) {
            return AWS_OP_ERR;
        }

        if (list->data) {
            memcpy(temp, list->data, list->current_size);

#ifdef DEBUG_BUILD
            memset(
                (void *)((uint8_t *)temp + list->current_size),
                AWS_ARRAY_LIST_DEBUG_FILL,
                new_size - list->current_size);
#endif
            aws_mem_release(list->alloc, list->data);
        }
        list->data = temp;
        list->current_size = new_size;
    }

    return AWS_OP_SUCCESS;
}

static void aws_array_list_mem_swap(void *AWS_RESTRICT item1, void *AWS_RESTRICT item2, size_t item_size) {
    enum { SLICE = 128 };

    assert(item1);
    assert(item2);

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

void aws_array_list_swap(struct aws_array_list *AWS_RESTRICT list, size_t a, size_t b) {
    assert(a < list->length);
    assert(b < list->length);
    if (a == b) {
        return;
    }

    void *item1 = NULL, *item2 = NULL;
    aws_array_list_get_at_ptr(list, &item1, a);
    aws_array_list_get_at_ptr(list, &item2, b);
    aws_array_list_mem_swap(item1, item2, list->item_size);
}
