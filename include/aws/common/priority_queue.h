#ifndef AWS_PRIORITY_QUEUE_H
#define AWS_PRIORITY_QUEUE_H
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
#include <aws/common/array_list.h>

/* The comparator should return a positive value if the second argument has a higher priority than the first; Otherwise,
 * it should return a negative value or zero.
 * NOTE: priority_queue pops its highest priority element first.
 * For example: int cmp(const void *a, const void *b) { return a < b; }
 * would result in a max heap, while:
 * int cmp(const void *a, const void *b) { return a > b; }
 * would result in a min heap.
 */
typedef int(*aws_priority_queue_compare)(const void *a, const void *b);

struct aws_priority_queue {
    /**
     * predicate that determines the priority of the elements in the queue.
     */
    aws_priority_queue_compare pred;

    /**
     * The underlying container storing the queue elements.
     */
    struct aws_array_list container;
};

#ifdef __cplusplus
extern "C" {
#endif

    /**
     * Initializes a priority queue struct for use. This mode will grow memory automatically (exponential model)
     * Default size is the inital size of the queue
     * item_size is the size of each element in bytes. Mixing items types is not supported by this API.
     * pred is the function that will be used to determine priority.
     */
    AWS_COMMON_API int aws_priority_queue_dynamic_init(struct aws_priority_queue *queue,
            struct aws_allocator *alloc, size_t default_size, size_t item_size, aws_priority_queue_compare pred);

    /**
     * Initializes a priority queue struct for use. This mode will not allocate any additional memory. When the heap fills
     * new enqueue operations will fail with AWS_ERROR_PRIORITY_QUEUE_FULL.
     * heap is the raw memory allocated for this priority_queue
     * item_count is the maximum number of elements the raw heap can contain
     * item_size is the size of each element in bytes. Mixing items types is not supported by this API.
     * pred is the function that will be used to determine priority.
     */
    AWS_COMMON_API void aws_priority_queue_static_init(struct aws_priority_queue *queue, void *heap, size_t item_count, 
            size_t item_size, aws_priority_queue_compare pred);

    /**
     * Cleans up any internally allocated memory and resets the struct for reuse or deletion.
     */
    AWS_COMMON_API void aws_priority_queue_clean_up(struct aws_priority_queue *queue);

    /**
     * Copies item into the queue and places it in the proper priority order. Complexity: O(log(n)).
     */
    AWS_COMMON_API int aws_priority_queue_push(struct aws_priority_queue *queue, void *item);

    /**
     * Copies the element of the highest priority, and removes it from the queue.. Complexity: O(log(n)).
     * If queue is empty, AWS_ERROR_PRIORITY_QUEUE_EMPTY will be raised.
     */
    AWS_COMMON_API int aws_priority_queue_pop(struct aws_priority_queue *queue, void *item);

    /**
     * Copies the element of the highest priority. Complexity: constant time.
     * If queue is empty, AWS_ERROR_PRIORITY_QUEUE_EMPTY will be raised.
     */
    AWS_COMMON_API int aws_priority_queue_top(struct aws_priority_queue *queue, void **item);

    /**
     * Current number of elements in the queue
     */
    AWS_COMMON_API size_t aws_priority_queue_size(struct aws_priority_queue *queue);

    /**
     * Current allocated capacity for the queue, in dynamic mode this grows over time, in static mode, this will never change.
     */
    AWS_COMMON_API size_t aws_priority_queue_capacity(struct aws_priority_queue *queue);

#ifdef __cplusplus
}
#endif

#endif /* #ifndef AWS_CORE_PRIORITY_QUEUE_H */
