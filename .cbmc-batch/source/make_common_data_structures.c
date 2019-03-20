/*
 * Copyright 2018 Amazon.com, Inc. or its affiliates. All Rights Reserved.
 *
 * Licensed under the Apache License, Version 2.0 (the "License"). You may not use
 * this file except in compliance with the License. A copy of the License is
 * located at
 *
 *     http://aws.amazon.com/apache2.0/
 *
 * or in the "license" file accompanying this file. This file is distributed on an
 * "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or
 * implied. See the License for the specific language governing permissions and
 * limitations under the License.
 */

#include "proof_helpers/make_common_data_structures.h"

/**
 * It nondeterministically creates either a static or dynamic array list
 * structure, which is bounded by item_count and item_size parameters.
 */
struct aws_array_list *make_arbitrary_array_list(size_t item_count, size_t item_size) {
    struct aws_array_list *list;
    /* Assume list is allocated */
    ASSUME_VALID_MEMORY(list);

    if (nondet_int()) { /* Dynamic initialization */
        /* Use default allocator */
        struct aws_allocator *allocator = malloc(sizeof(*allocator));
        ASSUME_DEFAULT_ALLOCATOR(allocator);
        __CPROVER_assume(!aws_array_list_init_dynamic(list, allocator, item_count, item_size));
    } else { /* Static initialization */
        __CPROVER_assume(item_count > 0);
        __CPROVER_assume(item_size > 0);

        size_t len = item_count * item_size;
        void *raw_array = malloc(len);

        aws_array_list_init_static(list, raw_array, item_count, item_size);
    }

    return list;
}
