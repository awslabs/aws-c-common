#ifndef AWS_COMMON_VECTOR_H
#define AWS_COMMON_VECTOR_H

/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */
#include <aws/common/array_list.h>

#define AWS_VECTOR_DEFAULT_CAPACITY 4

#define DECLARE_VECTOR(VECNAME, T)                                                                                     \
    _Pragma("GCC diagnostic push");                                                                                    \
    _Pragma("GCC diagnostic ignored \"-Wunused-function\"");                                                           \
    struct VECNAME {                                                                                                   \
        struct aws_array_list impl;                                                                                    \
    };                                                                                                                 \
                                                                                                                       \
    AWS_STATIC_IMPL void VECNAME##_init(struct VECNAME *AWS_RESTRICT vector, struct aws_allocator *alloc) {            \
        aws_array_list_init_dynamic(&vector->impl, alloc, AWS_VECTOR_DEFAULT_CAPACITY, sizeof(T));                     \
    }                                                                                                                  \
                                                                                                                       \
    AWS_STATIC_IMPL void VECNAME##_clean_up(struct VECNAME *AWS_RESTRICT vector) {                                     \
        aws_array_list_clean_up(&vector->impl);                                                                        \
    }                                                                                                                  \
                                                                                                                       \
    AWS_STATIC_IMPL size_t VECNAME##_length(const struct VECNAME *AWS_RESTRICT vector) {                               \
        return aws_array_list_length(&vector->impl);                                                                   \
    }                                                                                                                  \
                                                                                                                       \
    AWS_STATIC_IMPL size_t VECNAME##_capacity(const struct VECNAME *AWS_RESTRICT vector) {                             \
        return aws_array_list_length(&vector->impl);                                                                   \
    }                                                                                                                  \
                                                                                                                       \
    AWS_STATIC_IMPL bool VECNAME##_empty(const struct VECNAME *AWS_RESTRICT vector) {                                  \
        return aws_array_list_length(&vector->impl) == 0;                                                              \
    }                                                                                                                  \
                                                                                                                       \
    AWS_STATIC_IMPL void VECNAME##_push_back(struct VECNAME *AWS_RESTRICT vector, T val) {                             \
        aws_array_list_push_back(&vector->impl, &val);                                                                 \
    }                                                                                                                  \
                                                                                                                       \
    AWS_STATIC_IMPL T *VECNAME##_data(const struct VECNAME *AWS_RESTRICT vector) { return (T *)(vector->impl.data); }  \
                                                                                                                       \
    AWS_STATIC_IMPL T VECNAME##_get(const struct VECNAME *AWS_RESTRICT vector, size_t index) {                         \
        AWS_PRECONDITION(index < aws_array_list_length(&vector->impl));                                                \
        return VECNAME##_data(vector)[index];                                                                          \
    }                                                                                                                  \
                                                                                                                       \
    AWS_STATIC_IMPL int VECNAME##_get_checked(const struct VECNAME *AWS_RESTRICT vector, size_t index, T *out_val) {   \
        return aws_array_list_get_at(&vector->impl, out_val, index);                                                   \
    }                                                                                                                  \
                                                                                                                       \
    AWS_STATIC_IMPL T *VECNAME##_get_ptr(const struct VECNAME *AWS_RESTRICT vector, size_t index) {                    \
        AWS_PRECONDITION(index < aws_array_list_length(&vector->impl));                                                \
        return &VECNAME##_data(vector)[index];                                                                         \
    }                                                                                                                  \
                                                                                                                       \
    AWS_STATIC_IMPL int VECNAME##_get_ptr_checked(                                                                     \
        const struct VECNAME *AWS_RESTRICT vector, size_t index, T **out_ptr) {                                        \
        return aws_array_list_get_at_ptr(&vector->impl, (void **)out_ptr, index);                                      \
    }                                                                                                                  \
                                                                                                                       \
    AWS_STATIC_IMPL void VECNAME##_set(struct VECNAME *AWS_RESTRICT vector, size_t index, T val) {                     \
        AWS_PRECONDITION(index < aws_array_list_length(&vector->impl));                                                \
        VECNAME##_data(vector)[index] = val;                                                                           \
    }                                                                                                                  \
                                                                                                                       \
    AWS_STATIC_IMPL int VECNAME##_set_checked(struct VECNAME *AWS_RESTRICT vector, size_t index, T val) {              \
        if (AWS_UNLIKELY(index >= aws_array_list_length(&vector->impl))) {                                             \
            return aws_raise_error(AWS_ERROR_INVALID_INDEX);                                                           \
        }                                                                                                              \
        VECNAME##_data(vector)[index] = val;                                                                           \
        return AWS_OP_SUCCESS;                                                                                         \
    }                                                                                                                  \
    _Pragma("GCC diagnostic pop");

#endif /* AWS_COMMON_VECTOR_H */
