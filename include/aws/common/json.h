#ifndef AWS_COMMON_JSON_H
#define AWS_COMMON_JSON_H

/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */
#include "common.h"

struct aws_json_value;

// ====================
// Create and pass type

/**
 * Creates a new string aws_json_value with the given string and returns a pointer to it.
 *
 * Note: You will need to free the memory for the aws_json_value using aws_json_destroy on the aws_json_value or
 * on the object/array containing the aws_json_value.
 * @param cursor A byte pointer to the string you want to store in the aws_json_value
 * @param allocator The allocator to use when creating the value
 * @return A new string aws_json_value
 */
AWS_COMMON_API
struct aws_json_value *aws_json_string_new(const struct aws_byte_cursor *cursor, const struct aws_allocator *allocator);

/**
 * Creates a new number aws_json_value with the given number and returns a pointer to it.
 *
 * Note: You will need to free the memory for the aws_json_value using aws_json_destroy on the aws_json_value or
 * on the object/array containing the aws_json_value.
 * @param number The number you want to store in the aws_json_value
 * @param allocator The allocator to use when creating the value
 * @return A new number aws_json_value
 */
AWS_COMMON_API
struct aws_json_value *aws_json_number_new(const double number, const struct aws_allocator *allocator);

/**
 * Creates a new array aws_json_value and returns a pointer to it.
 *
 * Note: You will need to free the memory for the aws_json_value using aws_json_destroy on the aws_json_value or
 * on the object/array containing the aws_json_value.
 * Deleting this array will also destroy any aws_json_values it contains.
 * @param allocator The allocator to use when creating the value
 * @return A new array aws_json_value
 */
AWS_COMMON_API
struct aws_json_value *aws_json_array_new(const struct aws_allocator *allocator);

/**
 * Creates a new boolean aws_json_value with the given boolean and returns a pointer to it.
 *
 * Note: You will need to free the memory for the aws_json_value using aws_json_destroy on the aws_json_value or
 * on the object/array containing the aws_json_value.
 * @param boolean The boolean you want to store in the aws_json_value
 * @param allocator The allocator to use when creating the value
 * @return A new boolean aws_json_value
 */
AWS_COMMON_API
struct aws_json_value *aws_json_boolean_new(const bool boolean, const struct aws_allocator *allocator);

/**
 * Creates a new null aws_json_value and returns a pointer to it.
 *
 * Note: You will need to free the memory for the aws_json_value using aws_json_destroy on the aws_json_value or
 * on the object/array containing the aws_json_value.
 * @param allocator The allocator to use when creating the value
 * @return A new null aws_json_value
 */
AWS_COMMON_API
struct aws_json_value *aws_json_null_new(const struct aws_allocator *allocator);

/**
 * Creates a new object aws_json_value and returns a pointer to it.
 *
 * Note: You will need to free the memory for the aws_json_value using aws_json_destroy on the aws_json_value or
 * on the object/array containing the aws_json_value.
 * Deleting this object will also destroy any aws_json_values it contains.
 * @param allocator The allocator to use when creating the value
 * @return A new object aws_json_value
 */
AWS_COMMON_API
struct aws_json_value *aws_json_object_new(const struct aws_allocator *allocator);
// ====================

// ====================
// Value getters

/**
 * Gets the string of a string aws_json_value.
 * @param node The string aws_json_value.
 * @return The string of the string aws_json_value, otherwise NULL.
 */
AWS_COMMON_API
int aws_json_value_get_string(const struct aws_json_value *node, struct aws_byte_cursor *output);

/**
 * Gets the number of a number aws_json_value.
 * @param node The number aws_json_value.
 * @return The number of the number aws_json_value, otherwise NULL.
 */
AWS_COMMON_API
int aws_json_value_get_number(const struct aws_json_value *node, double *output);

/**
 * Gets the boolean of a boolean aws_json_value.
 * @param node The boolean aws_json_value.
 * @return The boolean of the boolean aws_json_value, otherwise false.
 */
AWS_COMMON_API
int aws_json_value_get_boolean(const struct aws_json_value *node, bool *output);
// ====================

// ====================
// Object API

/**
 * Adds a aws_json_value to a object aws_json_value.
 * @param object The object aws_json_value you want to add a node to.
 * @param key The key to add the aws_json_value at.
 * @param node The aws_json_value you want to add.
 * @return AWS_OP_SUCCESS if adding was successful, otherwise AWS_OP_ERR.
 */
AWS_COMMON_API
int aws_json_object_add(const struct aws_json_value *object, const struct aws_byte_cursor *cursor,
                        const struct aws_allocator *allocator, const struct aws_json_value *node);

/**
 * Returns the aws_json_value at the given key.
 * @param object The object aws_json_value you want to get the node from.
 * @param key The key that the aws_json_value is at. Is case sensitive.
 * @return The aws_json_value at the given key, otherwise NULL.
 */
AWS_COMMON_API
struct aws_json_value *aws_json_object_get(const struct aws_json_value *object, const struct aws_byte_cursor *cursor,
                                           const struct aws_allocator *allocator);

/**
 * Returns the aws_json_value at the given case insensitive key.
 * @param object The object aws_json_value you want to get the node from.
 * @param key The key that the aws_json_value is at. Is not case sensitive.
 * @return The aws_json_value at the given key, otherwise NULL.
 */
AWS_COMMON_API
struct aws_json_value *aws_json_object_get_insensitive(const struct aws_json_value *object,
                                                       const struct aws_byte_cursor *cursor,
                                                       const struct aws_allocator *allocator);

/**
 * Checks if there is a aws_json_value at the given key.
 * @param object The object aws_json_value you want to check a key in.
 * @param key The key that you want to check. Is case sensitive.
 * @return AWS_OP_SUCCESS if a aws_json_value is found, otherwise AWS_OP_ERR.
 */
AWS_COMMON_API
int aws_json_object_has(const struct aws_json_value *object, const struct aws_byte_cursor *cursor,
                        const struct aws_allocator *allocator);

/**
 * Removes the aws_json_value at the given key.
 * @param object The object aws_json_value you want to remove a aws_json_value in.
 * @param key The key that the aws_json_value is at. Is case sensitive.
 * @return AWS_OP_SUCCESS if the aws_json_value was removed, otherwise AWS_OP_ERR.
 */
AWS_COMMON_API
int aws_json_object_remove(const struct aws_json_value *object, const struct aws_byte_cursor *cursor,
                           const struct aws_allocator *allocator);
// ====================

// ====================
// Array API

/**
 * Adds a aws_json_value to the given array aws_json_value.
 * @param array The array aws_json_value you want to add an aws_json_value to.
 * @param node The aws_json_value you want to add.
 * @return AWS_OP_SUCCESS if adding the aws_json_value was successful, otherwise AWS_OP_ERR.
 */
AWS_COMMON_API
int aws_json_array_add(const struct aws_json_value *array, const struct aws_json_value *node);

/**
 * Returns the aws_json_value at the given index in the array aws_json_value.
 * @param array The array aws_json_value.
 * @param index The index of the aws_json_value you want to access.
 * @return A pointer to the aws_json_value at the given index in the array, otherwise NULL.
 */
AWS_COMMON_API
struct aws_json_value *aws_json_array_get(const struct aws_json_value *array, const size_t index);

/**
 * Returns the number of items in the array aws_json_value.
 * @param array The array aws_json_value.
 * @return The number of items in the array_json_node.
 */
AWS_COMMON_API
int aws_json_array_get_count(const struct aws_json_value *array);

/**
 * Removes the aws_json_value at the given index in the array aws_json_value.
 * @param array The array aws_json_value.
 * @param index The index containing the aws_json_value you want to remove.
 * @return AWS_OP_SUCCESS if the aws_json_value at the index was removed, otherwise AWS_OP_ERR.
 */
AWS_COMMON_API
int aws_json_array_remove(const struct aws_json_value *array, const size_t index);
// ====================

// ====================
// Checks

/**
 * Checks if the aws_json_value is a string.
 * @param node The aws_json_value to check.
 * @return AWS_OP_SUCCESS if the aws_json_value is a string aws_json_value, otherwise AWS_OP_ERR.
 */
AWS_COMMON_API
bool aws_json_is_string(const struct aws_json_value *node);

/**
 * Checks if the aws_json_value is a number.
 * @param node The aws_json_value to check.
 * @return AWS_OP_SUCCESS if the aws_json_value is a number aws_json_value, otherwise AWS_OP_ERR.
 */
AWS_COMMON_API
bool aws_json_is_number(const struct aws_json_value *node);

/**
 * Checks if the aws_json_value is a array.
 * @param node The aws_json_value to check.
 * @return AWS_OP_SUCCESS if the aws_json_value is a array aws_json_value, otherwise AWS_OP_ERR.
 */
AWS_COMMON_API
bool aws_json_is_array(const struct aws_json_value *node);

/**
 * Checks if the aws_json_value is a boolean.
 * @param node The aws_json_value to check.
 * @return AWS_OP_SUCCESS if the aws_json_value is a boolean aws_json_value, otherwise AWS_OP_ERR.
 */
AWS_COMMON_API
bool aws_json_is_boolean(const struct aws_json_value *node);

/**
 * Checks if the aws_json_value is a null aws_json_value.
 * @param node The aws_json_value to check.
 * @return AWS_OP_SUCCESS if the aws_json_value is a null aws_json_value, otherwise AWS_OP_ERR.
 */
AWS_COMMON_API
bool aws_json_is_null(const struct aws_json_value *node);

/**
 * Checks if the aws_json_value is a object aws_json_value.
 * @param node The aws_json_value to check.
 * @return AWS_OP_SUCCESS if the aws_json_value is a object aws_json_value, otherwise AWS_OP_ERR.
 */
AWS_COMMON_API
bool aws_json_is_object(const struct aws_json_value *node);
// ====================

// ====================
// Memory Management

/**
 * Initializes the JSON module for use.
 * @param allocator The allocator to use for creating aws_json_value structs.
 */
AWS_COMMON_API
void aws_json_module_init(const struct aws_allocator *allocator);

/**
 * Cleans up the JSON module. Should be called when finished using the module.
 */
AWS_COMMON_API
void aws_json_module_cleanup(void);

/**
 * Removes the aws_json_value from memory. If the aws_json_value is a object or array, it will also destroy
 * attached aws_json_values as well.
 * @param node The aws_json_value to destroy.
 * @return AWS_OP_SUCCESS if the destroy was successful, otherwise AWS_OP_ERR.
 */
AWS_COMMON_API
int aws_json_destroy(const struct aws_json_value *node);
// ====================

// ====================
// Utility

/**
 * Returns an unformatted JSON string representation of the aws_json_value.
 * @param node The aws_json_value to format.
 * @return A string containing the JSON.
 */
AWS_COMMON_API
struct aws_byte_buf *aws_json_to_string(const struct aws_json_value *node);

/**
 * Returns a formatted JSON string representation of the aws_json_value.
 * @param node The aws_json_value to format.
 * @return A string containing the JSON.
 */
AWS_COMMON_API
struct aws_byte_buf *aws_json_to_string_formatted(const struct aws_json_value *node);

/**
 * Parses the JSON string and returns a aws_json_value containing the root of the JSON.
 * @param string The string containing the JSON.
 * @return The root aws_json_value of the JSON.
 */
AWS_COMMON_API
struct aws_json_value *aws_json_from_string(const struct aws_byte_cursor *cursor, const struct aws_allocator *allocator);

/**
 * Determines if the aws_json_value is a valid aws_json_value.
 * @param node The aws_json_value to check.
 * @return AWS_OP_SUCCESS if the aws_json_value is valid, otherwise AWS_OP_ERR.
 */
AWS_COMMON_API
int aws_json_is_valid(const struct aws_json_value *node);
// ====================

#endif // AWS_COMMON_JSON_H
