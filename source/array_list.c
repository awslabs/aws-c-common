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

int aws_array_list_init_dynamic(struct aws_array_list *list,
    struct aws_allocator *alloc, size_t initial_item_allocation, size_t item_size) {
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
        memset(list->data, 0, allocation_size);
        list->current_size = allocation_size;
    }

    return AWS_OP_SUCCESS;
}

int aws_array_list_init_static(struct aws_array_list *list, void *raw_array, size_t array_size, size_t item_size) {
    assert(raw_array);
    assert(array_size >= item_size);
    list->current_size = array_size;
    list->item_size = item_size;
    list->length = 0;
    list->data = raw_array;
    list->alloc = NULL;
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
    list->alloc = 0;
}

int aws_array_list_push_back(struct aws_array_list *list, const void *val) {

    size_t filled_space = list->length  * list->item_size;
    if (filled_space == list->current_size) {
        if (list->alloc) {
            size_t new_size = list->current_size << 1;
            if (new_size == 0) {
                new_size = 2;
            }

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

            memset((uint8_t *)temp + list->length, 0, new_size - list->current_size);

            if (list->data) {
                memcpy(temp, list->data, list->current_size);
                aws_mem_release(list->alloc, list->data);
            }

            list->data = temp;
            list->current_size = new_size;
        }
        else {
            return aws_raise_error(AWS_ERROR_LIST_EXCEEDS_MAX_SIZE);
        }
    }

    memcpy((void *)((uint8_t *)list->data + filled_space), val, list->item_size);
    list->length++;
    return AWS_OP_SUCCESS;
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
        memset((void *)((uint8_t *)list->data + last_bytes), 0, list->item_size);
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
        memset(list->data, 0, list->current_size);
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

size_t aws_array_list_size(const struct aws_array_list *list) {
    return list->current_size;
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

int aws_array_list_set_at(struct aws_array_list *list, const void *val, size_t index) {
    if (list->current_size > index * list->item_size) {
        memcpy((void *)((uint8_t *)list->data + (list->item_size * index)), val, list->item_size);

        /* this isn't perfect but its the best I can come up with for detecting length changes*/
        if (index >= list->length) {
            list->length = index + 1;
        }
        return AWS_OP_SUCCESS;
    }
    return aws_raise_error(AWS_ERROR_INVALID_INDEX);
}

