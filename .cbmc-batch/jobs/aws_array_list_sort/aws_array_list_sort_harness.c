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
#include <proof_helpers/make_common_data_structures.h>

/* These values allow us to reach a higher coverage rate */
#define MAX_ITEM_SIZE 2
#define MAX_INITIAL_ITEM_ALLOCATION (UINT64_MAX / MAX_ITEM_SIZE) + 1

/**
 * Standard implementation of compare function for qsort
 */
int compare(const void *a, const void *b, size_t item_size) {
    int res;
    __CPROVER_precondition(__CPROVER_r_ok(a, item_size), "first element readable in compare function");
    __CPROVER_precondition(__CPROVER_r_ok(b, item_size), "second element readable in compare function");
    return res;
}

/**
 * Runtime: 0m3.399s
 */
void aws_array_list_sort_harness() {
    struct aws_array_list *list;
    /*
     * Assumptions:
     *     - a valid non-deterministic aws_array_list bounded by initial_item_allocation and item_size;
     *     - non-deterministic list->initial_item_allocation <= MAX_INITIAL_ITEM_ALLOCATION;
     *     - non-deterministic list->item_size <= MAX_ITEM_SIZE;
     *     - non-deterministic list->length <= initial_item_allocation;
     */
    ASSUME_BOUNDED_ARRAY_LIST(list, MAX_INITIAL_ITEM_ALLOCATION, MAX_ITEM_SIZE);

    struct aws_allocator *alloc = list->alloc;
    size_t current_size = list->current_size;
    size_t length = list->length;
    size_t item_size = list->item_size;
    void *data = list->data;

    aws_array_list_sort(list, compare);

    assert(list->alloc == alloc);
    assert(list->current_size == current_size);
    assert(list->length == length);
    assert(list->item_size == item_size);
    assert(list->data == data);
}
