#ifndef AWS_COMMON_hash_table_H
#define AWS_COMMON_hash_table_H

/*
* Copyright 2010-2017 Amazon.com, Inc. or its affiliates. All Rights Reserved.
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

#define AWS_COMMON_HASH_TABLE_ITER_CONTINUE 0
#define AWS_COMMON_HASH_TABLE_ITER_DELETE 1
#define AWS_COMMON_HASH_TABLE_ITER_STOP 2

/**
 * Hash table data structure. This module provides an automatically resizing
 * hash table implementation for general purpose use. The hash table stores a
 * mapping between void * keys and values; it is expected that in most cases,
 * these will point to a structure elsewhere in the heap, instead of inlining a
 * key or value into the hash table element itself.
 *
 * Currently, this hash table implements a variant of robin hood hashing, but
 * we do not guarantee that this won't change in the future.
 *
 * Associated with each hash function are three callbacks:
 *
 *   hash_fn - A hash function from the keys to a uint64_t. It is critical that
 *      the hash function for a key does not change while the key is in the hash
 *      table; violating this results in undefined behavior. Collisions are
 *      tolerated, though naturally with reduced performance.
 *
 *   equals_fn - An equality comparison function. This function must be
 *      reflexive and consistent with hash_fn.
 *
 *   destroy_fn - An optional callback invoked when an element is removed from
 *      the table. This operation is invoked only if the operation that removes
 *      the element does not also return the removed element. This allows
 *      callers to decide whether they want to take ownership of the element,
 *      or to allow it to be implicitly deleted.
 *
 * This datastructure can be safely moved between threads, subject to the
 * requirements of the underlying allocator. It is also safe to invoke
 * non-mutating operations on the hash table from multiple threads. A suitable
 * memory barrier must be used when transitioning from single-threaded mutating
 * usage to multithreaded usage.
 */
struct aws_common_hash_table {
    void *pImpl;
};

/**
 * Represents an element in the hash table. Various operations on the hash
 * table may provide pointers to elements stored within the hash table;
 * generally, calling code may alter value, but must not alter key (or any
 * information used to compute key's hash code).
 *
 * Pointers to elements within the hash are invalidated whenever an operation
 * which may change the number of elements in the hash is invoked (i.e. put,
 * delete, clear, and clean_up), regardless of whether the number of elements
 * actually changes.
 */
struct aws_common_hash_element {
    const void *key;
    void *value;
};

/**
 * Prototype for a key hashing function pointer.
 */
typedef uint64_t (*aws_hash_fn_t)(const void *key);

/**
 * Prototype for a hash table equality check function.
 *
 * Equality functions used in a hash table must be reflexive (i.e., a == b if
 * and only if b == a), and must be consistent with the hash function in use.
 */
typedef int (*aws_equals_fn_t)(const void *a, const void *b);

/*
 * This callback is used to destroy elements that are not returned to the
 * calling code during destruction.  In general, if the element is returned to
 * calling code, calling code must destroy it.
 */
typedef void (*aws_hash_element_destroy_t)(
    struct aws_common_hash_element element
);

#ifdef __cplusplus
extern "C" {
#endif

    /**
     * Initializes a hash map with initial capacity for 'size' elements
     * without resizing. Uses hash_fn to compute the hash of each element.
     * equals_fn to compute equality of two keys.  destroy_fn is called whenver
     * an element is removed without being returned, and may be NULL if a
     * callback is not desired in this case.
     */

    AWS_COMMON_API int aws_common_hash_table_init(
        struct aws_common_hash_table *map,
        struct aws_allocator *alloc, size_t size,
        aws_hash_fn_t hash_fn,
        aws_equals_fn_t equals_fn,
        aws_hash_element_destroy_t destroy_fn);

    /**
     * Deletes every element from map and frees all associated memory.
     * destroy_fn will be called for each element.  aws_common_hash_table_init
     * must be called before reusing the hash table.
     */
    AWS_COMMON_API void aws_common_hash_table_clean_up(
        struct aws_common_hash_table *map);

    /**
     * Attempts to locate an element at key.  If the element is found, a
     * pointer to the value is placed in *pElem, and AWS_ERROR_SUCCESS is
     * returned. Otherwise, *pElem is unchanged, and
     * AWS_ERROR_HASHTBL_ITEM_NOT_FOUND is returned.
     *
     * This method does not change the state of the hash table. Therefore, it
     * is safe to call _find from multiple threads on the same hash table,
     * provided no mutating operations happen in parallel.
     *
     * Calling code may update the value in the hash table by modifying **pElem
     * after a successful find. However, this pointer is not guaranteed to
     * remain usable after a subsequent call to _put, _delete, _clear, or
     * _clean_up.
     */

    AWS_COMMON_API int aws_common_hash_table_find(
        struct aws_common_hash_table *map,
        const void *key, struct aws_common_hash_element **pElem);

    /**
     * Attempts to locate an element at key. If no such element was found,
     * creates a new element, with value initialized to NULL. In either case, a
     * pointer to the element is placed in *pElem.
     *
     * If was_created is non-NULL, *was_created is set to 0 if an existing
     * element was found, or 1 is a new element was created.
     *
     * Returns AWS_ERROR_SUCCESS if an item was found or created.
     * Returns AWS_ERROR_OOM if hash table expansion was required and memory
     * allocation failed.
     */
    AWS_COMMON_API int aws_common_hash_table_create(
        struct aws_common_hash_table *map,
        const void *key, struct aws_common_hash_element **pElem,
        int *was_created
    );

    /**
     * Removes element at key. If the element is not found,
     * AWS_ERROR_HASHTBL_ITEM_NOT_FOUND is returned; otherwise
     * AWS_ERROR_SUCCESS is returned.
     *
     * If pValue is non-NULL, the existing value (if any) is moved into
     * (*value) before removing from the table, and destroy_fn is _not_
     * invoked. If pValue is NULL, then (if the element existed) destroy_fn
     * will be invoked on the element being removed.
     */
    AWS_COMMON_API int aws_common_hash_table_remove(
        struct aws_common_hash_table *map,
        const void *key, struct aws_common_hash_element *pValue
    );

    /**
     * Iterates through every element in the map and invokes the callback on
     * that item.
     *
     * The callback may change the value associated with the key by overwriting
     * the value pointed-to by value. In this case, the on_element_removed
     * callback will not be invoked, unless the callback invokes
     * AWS_COMMON_HASH_TABLE_ITER_DELETE (in which case the on_element_removed
     * is given the updated value).
     *
     * The callback must return one of the following values:
     * # AWS_COMMON_HASH_TABLE_ITER_CONTINUE - Continues iteration to the next
     *     element
     * # AWS_COMMON_HASH_TABLE_ITER_DELETE   - Deletes the current value and
     *     continues iteration.  destroy_fn will NOT be invoked.
     * # AWS_COMMON_HASH_TABLE_ITER_STOP     - Stops iterating through the hash
     *     table
     *
     * Invoking any method which may change the contents of the hashtable
     * during iteration results in undefined behavior. However, you may safely
     * invoke non-mutating operations during an iteration.
     *
     * This operation is mutating only if AWS_COMMON_HASH_TABLE_ITER_DELETE
     * is returned at some point during iteration. Otherwise, it is non-mutating
     * and is safe to invoke in parallel with other non-mutating operations.
     */

    AWS_COMMON_API int aws_common_hash_table_foreach(
        struct aws_common_hash_table *map,
        int (*callback)(void *context, struct aws_common_hash_element *pElement),
        void *context);

    /**
     * Removes every element from the hash map. destroy_fn will be called for
     * each element.
     */
    AWS_COMMON_API void aws_common_hash_table_clear(
        struct aws_common_hash_table *map);

    /**
     * Convenience hash function for NUL-terminated strings
     */
    AWS_COMMON_API uint64_t aws_common_hash_string(const void *a);

    /**
     * Convenience eq function for NUL-terminated strings
     */
    AWS_COMMON_API int aws_common_string_eq(const void *a, const void *b);

    /**
     * Convenience hash function which hashes the pointer value directly,
     * without dereferencing.  This can be used in cases where pointer identity
     * is desired, or where a uintptr_t is encoded into a const void *.
     */
    AWS_COMMON_API uint64_t aws_common_hash_ptr(const void *a);

    /**
     * Equality function which compares pointer equality.
     */
    AWS_COMMON_API int aws_common_ptr_eq(const void *a, const void *b);

#ifdef _cplusplus
}
#endif


#endif /* AWS_COMMON_hash_table_H */


