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

struct aws_array_list {
    struct aws_allocator *alloc;
    size_t current_size;
    size_t length;
    size_t item_size;
    void *data;
};

/**
 * Prototype for a comparator function for sorting elements.
 *
 * a and b should be cast to pointers to the element type held in the list
 * before being dereferenced. The function should compare the elements and
 * return a positive number if a > b, zero if a = b, and a negative number
 * if a < b.
 */
typedef int (*aws_array_list_comparator)(const void *a, const void *b);

#ifdef __cplusplus
extern "C" {
#endif

    /**
    * Initializes an array list with an array of size initial_item_allocation * item_size. In this mode, the array size will grow
    * by a factor of 2 upon insertion if space is not available. initial_item_allocation is the number of elements
    * you want space allocated for. item_size is the size of each element in bytes. Mixing items types is not supported
    * by this API.
    */
    AWS_COMMON_API int aws_array_list_init_dynamic(struct aws_array_list *list,
        struct aws_allocator *alloc, size_t initial_item_allocation, size_t item_size);

    /**
    * Initializes an array list with a preallocated array of void *. item_count is the number of elements in the array,
    * and item_size is the size in bytes of each element. Mixing items types is not supported
    * by this API. Once this list is full, new items will be rejected.
    */
    AWS_COMMON_API void aws_array_list_init_static(struct aws_array_list *list,
        void *raw_array, size_t item_count, size_t item_size);

    /**
    * Deallocates any memory that was allocated for this list, and resets list for reuse or deletion.
    */
    AWS_COMMON_API void aws_array_list_clean_up(struct aws_array_list *list);

    /**
    * Pushes the memory pointed to by val onto the end of internal list
    */
    AWS_COMMON_API int aws_array_list_push_back(struct aws_array_list *list, const void *val);

    /**
    * Copies the element at the front of the list if it exists. If list is empty, AWS_ERROR_LIST_EMPTY will be raised
    */
    AWS_COMMON_API int aws_array_list_front(const struct aws_array_list *list, void *val);

    /**
    * Deletes the element at the front of the list if it exists. If list is empty, AWS_ERROR_LIST_EMPTY will be raised.
    * This call results in shifting all of the elements at the end of the array to the front. Avoid this call unless that is intended
    * behavior.
    */
    AWS_COMMON_API int aws_array_list_pop_front(struct aws_array_list *list);

    /**
     * Delete N elements from the front of the list.
     * Remaining elements are shifted to the front of the list.
     * If the list has less than N elements, the list is cleared.
     * This call is more efficient than calling aws_array_list_pop_front() N times.
     */
    AWS_COMMON_API void aws_array_list_pop_front_n(struct aws_array_list *list, size_t n);

    /**
     * Copies the element at the end of the list if it exists. If list is empty, AWS_ERROR_LIST_EMPTY will be raised.
     */
    AWS_COMMON_API int aws_array_list_back(const struct aws_array_list *list, void *val);

    /**
    * Deletes the element at the end of the list if it exists. If list is empty, AWS_ERROR_LIST_EMPTY will be raised.
    */
    AWS_COMMON_API int aws_array_list_pop_back(struct aws_array_list *list);

    /**
     * Clears all elements in the array and resets length to zero. Size does not change in this operation.
     */
    AWS_COMMON_API void aws_array_list_clear(struct aws_array_list *list);

    /**
     * If in dynamic mode, shrinks the allocated array size to the minimum amount necessary to store its elements.
     */
    AWS_COMMON_API int aws_array_list_shrink_to_fit(struct aws_array_list *list);

    /**
     * Copies the elements from from to to. If to is in static mode, it must at least be the same length as from. Any data
     * in to will be overwritten in this copy.
     */
    AWS_COMMON_API int aws_array_list_copy(const struct aws_array_list *from, struct aws_array_list *to);

    /**
     * Swap contents between two dynamic lists. Both lists must use the same allocator.
     */
    AWS_COMMON_API void aws_array_list_swap_contents(struct aws_array_list *list_a, struct aws_array_list *list_b);

    /**
     * Returns the number of elements that can fit in the internal array. If list is initialized in dynamic mode,
     * the capacity changes over time.
     */
    AWS_COMMON_API size_t aws_array_list_capacity(const struct aws_array_list *list);

    /**
     * Returns the number of elements in the internal array.
     */
    AWS_COMMON_API size_t aws_array_list_length(const struct aws_array_list *list);

    /**
     * Copies the memory at index to val. If element does not exist, AWS_ERROR_INVALID_INDEX will be raised.
     */
    AWS_COMMON_API int aws_array_list_get_at(const struct aws_array_list *list, void *val, size_t index);

    /**
     * Copies the memory address of the element at index to *val. If element does not exist, AWS_ERROR_INVALID_INDEX will be raised.
     */
    AWS_COMMON_API int aws_array_list_get_at_ptr(const struct aws_array_list *list, void **val, size_t index);

    /**
     * Copies the the memory pointed to by val into the array at index. If in dynamic mode, the size will grow by a factor of two
     * when the array is full. In static mode, AWS_ERROR_INVALID_INDEX will be raised if the index is past the bounds of the array.
     */
    AWS_COMMON_API int aws_array_list_set_at(struct aws_array_list *list, const void *val, size_t index);

    /**
     * Swap elements at the specified indices.
     */
    AWS_COMMON_API void aws_array_list_swap(struct aws_array_list *list, size_t a, size_t b);

    /**
     * Sort elements in the list in-place according to the comparator function.
     */
    AWS_COMMON_API void aws_array_list_sort(struct aws_array_list *list, aws_array_list_comparator compare_fn);

#ifdef __cplusplus
}
#endif

#endif /* AWS_COMMON_ARRAY_LIST_H */
