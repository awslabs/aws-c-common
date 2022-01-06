#ifndef AWS_COMMON_RANDOM_ACCESS_SET_H
#define AWS_COMMON_RANDOM_ACCESS_SET_H

/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/common/array_list.h>
#include <aws/common/common.h>
#include <aws/common/hash_table.h>

struct aws_random_access_set_impl;

struct aws_random_access_set {
    struct aws_random_access_set_impl *impl;
};

AWS_EXTERN_C_BEGIN

/* TODO: CBMC verification. */
/**
 * Initialize the set, which support constant time of insert, remove and get random element
 * from the data structure.
 *
 * The underlying hash map will use hash_fn to compute the hash of each element. equals_fn to compute equality of two
 * keys.
 *
 * @param set                       Pointer of structure to initialize with
 * @param allocator                 Allocator
 * @param hash_fn                   Compute the hash of each element
 * @param equals_fn                 Compute equality of two elements
 * @param destroy_element_fn        Optional. Called when the element is removed
 * @param element_size              Size of each element
 * @param initial_item_allocation   The initial number of item to allocate.
 * @return AWS_OP_ERR if any fails to initialize, AWS_OP_SUCCESS on success.
 */
AWS_COMMON_API
int aws_random_access_set_init(
    struct aws_random_access_set *set,
    struct aws_allocator *allocator,
    aws_hash_fn *hash_fn,
    aws_hash_callback_eq_fn *equals_fn,
    aws_hash_callback_destroy_fn *destroy_element_fn,
    size_t element_size,
    size_t initial_item_allocation);

AWS_COMMON_API
void aws_random_access_set_clean_up(struct aws_random_access_set *set);

/**
 * Insert the element to the end of the array list. A map from the element to the index of it to the hash table.
 */
AWS_COMMON_API
int aws_random_access_set_insert(struct aws_random_access_set *set, const void *element);

/**
 * Find and remove the element from the table. If the element does not exist, or the table is empty, nothing will
 * happen. Switch the element with the end of the arraylist if needed. Remove the end of the arraylist
 */
AWS_COMMON_API
int aws_random_access_set_remove(struct aws_random_access_set *set, const void *element);

/**
 * Get a random element from the data structure. Fails when the data structure is empty.
 */
AWS_COMMON_API
int aws_random_access_set_get_random(struct aws_random_access_set *set, void *out);

AWS_COMMON_API
size_t aws_random_access_set_get_size(struct aws_random_access_set *set);

/**
 * Check the element exist in the data structure or not.
 */
AWS_COMMON_API
bool aws_random_access_set_exist(struct aws_random_access_set *set, const void *element);

/* TODO: Other operations: iterate through, find/check exist? */

AWS_EXTERN_C_END
#endif /* AWS_COMMON_RANDOM_ACCESS_SET_H */
