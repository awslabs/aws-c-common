#ifndef AWS_COMMON_ARRAY_LIST_H
#define AWS_COMMON_ARRAY_LIST_H

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

#include <aws/common/common.h>
#include <aws/common/error.h>
#include <stdint.h>
#include <string.h>

/* To declare an instance of a typed array use this macro (it's largely for header files). Then use the definition macro
 * for your .c file */
#define aws_typed_array_list_declaration(name, T)                                                                      \
struct aws_##name##_array_list {                                                                                       \
    struct aws_allocator *alloc;                                                                                       \
    size_t current_size;                                                                                               \
    size_t length;                                                                                                     \
                                                                                                                       \
    T *data;                                                                                                           \
};

/* To define your typed array list, use this macro (most likely in your .c file) */
#define aws_typed_array_list_definition(name, T)                                                                       \
                                                                                                                       \
/**
* Initializes an array list with an array of T of initial_size. In this mode, the array size will grow
* by a factor of 2 upon insertion if space is not available.
*/                                                                                                                     \
static inline int aws_##name##_array_list_init_dynamic(struct aws_##name##_array_list *list,                           \
                        struct aws_allocator *alloc, size_t initial_size) {                                            \
                                                                                                                       \
    list->alloc = alloc;                                                                                               \
    list->current_size = initial_size;                                                                                 \
    list->data = (T *)aws_mem_acquire(list->alloc, initial_size * sizeof(T));                                          \
    list->length = 0;                                                                                                  \
    if (!list->data) {                                                                                                 \
        return aws_raise_error(AWS_ERROR_OOM);                                                                         \
    }                                                                                                                  \
    memset(list->data, 0, initial_size * sizeof(T));                                                                   \
                                                                                                                       \
    return AWS_OP_SUCCESS;                                                                                             \
}                                                                                                                      \
                                                                                                                       \
/**
* Initializes an array list with a preallocated array of T of size array_size. When this list is full, it will reject
* insertions.
*/                                                                                                                     \
static inline int aws_##name##_array_list_init_static(struct aws_##name##_array_list *list,                            \
                        T *raw_array, size_t array_size) {                                                             \
                                                                                                                       \
    list->current_size = array_size;                                                                                   \
    list->length = 0;                                                                                                  \
    list->data = raw_array;                                                                                            \
    list->alloc = 0;                                                                                                   \
    return AWS_OP_SUCCESS;                                                                                             \
}                                                                                                                      \
                                                                                                                       \
/**
* Deallocates any memory that was allocated for this list, and resets list for reuse or deletion.
*/                                                                                                                     \
static inline void aws_##name##_array_list_clean_up(struct aws_##name##_array_list *list) {                            \
                                                                                                                       \
    if (list->alloc) {                                                                                                 \
        aws_mem_release(list->alloc, (void *)list->data);                                                              \
    }                                                                                                                  \
                                                                                                                       \
    list->current_size = 0;                                                                                            \
    list->length = 0;                                                                                                  \
    list->data = 0;                                                                                                    \
    list->alloc = 0;                                                                                                   \
}                                                                                                                      \
                                                                                                                       \
/**
* Pushes a the dereferenced value of val onto the end of internal list->
*/                                                                                                                     \
static inline int aws_##name##_array_list_push_back(struct aws_##name##_array_list *list, T *val) {                    \
                                                                                                                       \
    if (list->length == list->current_size) {                                                                          \
        if (list->alloc) {                                                                                             \
            size_t new_size = list->current_size << 1;                                                                 \
            T *temp = (T *)aws_mem_acquire(list->alloc, sizeof( T ) * new_size);                                       \
                                                                                                                       \
            if (!temp) {                                                                                               \
                return aws_raise_error(AWS_ERROR_OOM);                                                                 \
            }                                                                                                          \
            memset(temp + list->length, 0, (new_size - list->length) * sizeof( T ));                                   \
                                                                                                                       \
            list->current_size = new_size;                                                                             \
            memcpy(temp, list->data, list->length * sizeof( T ));                                                      \
            aws_mem_release(list->alloc, list->data);                                                                  \
            list->data = temp;                                                                                         \
        }                                                                                                              \
        else {                                                                                                         \
            return aws_raise_error(AWS_ERROR_LIST_EXCEEDS_MAX_SIZE);                                                   \
        }                                                                                                              \
    }                                                                                                                  \
                                                                                                                       \
    list->data[list->length++] = *val;                                                                                 \
    return AWS_OP_SUCCESS;                                                                                             \
}                                                                                                                      \
                                                                                                                       \
/**
* Returns the element at the front of the list if it exists. If list is empty, AWS_CORE_LIST_ERROR_EMPTY will be returned
*/                                                                                                                     \
static inline int aws_##name##_array_list_front(const struct aws_##name##_array_list *list, T *val)  {                 \
                                                                                                                       \
    if (list->length > 0) {                                                                                            \
        *val = list->data[0];                                                                                          \
        return AWS_OP_SUCCESS;                                                                                         \
    }                                                                                                                  \
                                                                                                                       \
    return aws_raise_error(AWS_ERROR_LIST_EMPTY);                                                                      \
}                                                                                                                      \
                                                                                                                       \
/**
* Deletes the element at the front of the list if it exists. If list is empty, AWS_CORE_LIST_ERROR_EMPTY will be returned.
* This call results in shifting all of the elements at the end of the array to the front. Avoid this call unless that is intended
* behavior.
*/                                                                                                                     \
static inline int aws_##name##_array_list_pop_front(struct aws_##name##_array_list *list) {                            \
                                                                                                                       \
    if (list->length > 0) {                                                                                            \
                                                                                                                       \
        memmove(list->data, list->data + 1, sizeof( T ) * (list->length - 1));                                         \
        memset(list->data + list->length - 1, 0, sizeof(T));                                                           \
                                                                                                                       \
        list->length--;                                                                                                \
        return AWS_OP_SUCCESS;                                                                                         \
    }                                                                                                                  \
                                                                                                                       \
    return aws_raise_error(AWS_ERROR_LIST_EMPTY);                                                                      \
}                                                                                                                      \
                                                                                                                       \
/**
* Returns the element at the end of the list if it exists. If list is empty, AWS_CORE_LIST_ERROR_EMPTY will be returned
*/                                                                                                                     \
static inline int aws_##name##_array_list_back(const struct aws_##name##_array_list *list, T *val) {                   \
    if (list->length > 0) {                                                                                            \
        *val = list->data[list->length - 1];                                                                           \
        return AWS_OP_SUCCESS;                                                                                         \
    }                                                                                                                  \
                                                                                                                       \
    return aws_raise_error(AWS_ERROR_LIST_EMPTY);                                                                      \
}                                                                                                                      \
                                                                                                                       \
/**
* Deletes the element at the end of the list if it exists. If list is empty, AWS_CORE_LIST_ERROR_EMPTY will be returned.
*/                                                                                                                     \
static inline int aws_##name##_array_list_pop_back(struct aws_##name##_array_list *list)  {                            \
                                                                                                                       \
    if (list->length > 0) {                                                                                            \
        memset(list->data + list->length - 1, 0, sizeof(T));                                                           \
        list->length--;                                                                                                \
        return AWS_OP_SUCCESS;                                                                                         \
    }                                                                                                                  \
                                                                                                                       \
    return aws_raise_error(AWS_ERROR_LIST_EMPTY);                                                                      \
}                                                                                                                      \
                                                                                                                       \
/**
* Clears all elements in the array and resets length to zero. Size does not change in this operation.
*/                                                                                                                     \
static inline void aws_##name##_array_list_clear(struct aws_##name##_array_list *list) {                               \
    memset(list->data, 0, sizeof(T) * list->length);                                                                   \
    list->length = 0;                                                                                                  \
}                                                                                                                      \
                                                                                                                       \
/**
* If in dynamic mode, shrinks the allocated array size to the minimum amount necessary to store its elements.
*/                                                                                                                     \
static inline int aws_##name##_array_list_shrink_to_fit(struct aws_##name##_array_list *list) {                        \
    if (list->alloc) {                                                                                                 \
        if (list->length < list->current_size) {                                                                       \
            T *raw_data = (T *)aws_mem_acquire(list->alloc, sizeof(T) * list->length);                                 \
                                                                                                                       \
            if (!raw_data) {                                                                                           \
                return aws_raise_error(AWS_ERROR_OOM);                                                                 \
            }                                                                                                          \
                                                                                                                       \
            memcpy(raw_data, list->data, list->length * sizeof(T));                                                    \
            aws_mem_release(list->alloc, (void *)list->data);                                                          \
            list->data = raw_data;                                                                                     \
            list->current_size = list->length;                                                                         \
        }                                                                                                              \
                                                                                                                       \
        return AWS_OP_SUCCESS;                                                                                         \
    }                                                                                                                  \
                                                                                                                       \
    return aws_raise_error(AWS_ERROR_LIST_STATIC_MODE_CANT_SHRINK);                                                    \
}                                                                                                                      \
                                                                                                                       \
/**
* Copies the elements from from to to. to must at least be the same length as from.
*/                                                                                                                     \
static inline int aws_##name##_array_list_copy(const struct aws_##name##_array_list *from,                             \
                        struct aws_##name##_array_list *to) {                                                          \
    if (to->current_size >= from->length) {                                                                            \
        memcpy(to->data, from->data, from->length * sizeof(T));                                                        \
        to->length = from->length;                                                                                     \
        return AWS_OP_SUCCESS;                                                                                         \
    }                                                                                                                  \
                                                                                                                       \
    return aws_raise_error(AWS_ERROR_LIST_DEST_COPY_TOO_SMALL);                                                        \
}                                                                                                                      \
                                                                                                                       \
/**
* Returns the current allocated size of the internal array. If list is initialized in dynamic mode, this size changes
* over time.
*/                                                                                                                     \
static inline size_t aws_##name##_array_list_size(const struct aws_##name##_array_list *list) {                        \
    return list->current_size;                                                                                         \
}                                                                                                                      \
                                                                                                                       \
/**
* Returns the number of elements in the internal array.
*/                                                                                                                     \
static inline size_t aws_##name##_array_list_length(const struct aws_##name##_array_list *list) {                      \
    return list->length;                                                                                               \
}                                                                                                                      \
                                                                                                                       \
/**
* Copies the dereferenced value of the pointer at index into val.
*/                                                                                                                     \
static inline int aws_##name##_array_list_get_at(const struct aws_##name##_array_list *list,                           \
                            T *val, size_t index) {                                                                    \
    if (list->current_size > index) {                                                                                  \
        *val = list->data[index];                                                                                      \
        return AWS_OP_SUCCESS;                                                                                         \
    }                                                                                                                  \
                                                                                                                       \
    return aws_raise_error(AWS_ERROR_INVALID_INDEX);                                                                   \
}                                                                                                                      \
                                                                                                                       \
/**
* Copies the dereferenced value of val into the array at index.
*/                                                                                                                     \
static inline int aws_##name##_array_list_set_at(struct aws_##name##_array_list *list,                                 \
                        T *val, size_t index) {                                                                        \
    if (list->current_size > index) {                                                                                  \
        list->data[index] = *val;                                                                                      \
                                                                                                                       \
        if (index >= list->length) {                                                                                   \
            list->length = index + 1;                                                                                  \
        }                                                                                                              \
                                                                                                                       \
        return AWS_OP_SUCCESS;                                                                                         \
    }                                                                                                                  \
                                                                                                                       \
    return aws_raise_error(AWS_ERROR_INVALID_INDEX);                                                                   \
}                                                                                                                      \

#endif /*AWS_COMMON_ARRAY_LIST_H */
