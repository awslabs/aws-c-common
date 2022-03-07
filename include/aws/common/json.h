#ifndef AWS_COMMON_JSON_JSON_H
#define AWS_COMMON_JSON_JSON_H

/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */
#include "thread.h"

AWS_COMMON_API
struct aws_json_node;

// ====================
// Create and pass type

/**
 * Creates a new aws_json_node and returns a pointer to it.
 *
 * Note: You will need to free the memory for the aws_json_node using aws_json_delete on the aws_json_node or
 * on the object/array containing the aws_json_node.
 * @return A new aws_json_node
 */
AWS_COMMON_API
struct aws_json_node *aws_json_node_new(void);

/**
 * Creates a new string aws_json_node with the given string and returns a pointer to it.
 *
 * Note: You will need to free the memory for the aws_json_node using aws_json_delete on the aws_json_node or
 * on the object/array containing the aws_json_node.
 * @param string The string you want to store in the aws_json_node
 * @return A new string aws_json_node
 */
AWS_COMMON_API
struct aws_json_node *aws_json_string_new(char *string);

/**
 * Creates a new number aws_json_node with the given number and returns a pointer to it.
 *
 * Note: You will need to free the memory for the aws_json_node using aws_json_delete on the aws_json_node or
 * on the object/array containing the aws_json_node.
 * @param number The number you want to store in the aws_json_node
 * @return A new number aws_json_node
 */
AWS_COMMON_API
struct aws_json_node *aws_json_number_new(double number);

/**
 * Creates a new array aws_json_node and returns a pointer to it.
 *
 * Note: You will need to free the memory for the aws_json_node using aws_json_delete on the aws_json_node or
 * on the object/array containing the aws_json_node.
 * Deleting this array will also delete any aws_json_nodes it contains.
 * @return A new array aws_json_node
 */
AWS_COMMON_API
struct aws_json_node *aws_json_array_new(void);

/**
 * Creates a new boolean aws_json_node with the given boolean and returns a pointer to it.
 *
 * Note: You will need to free the memory for the aws_json_node using aws_json_delete on the aws_json_node or
 * on the object/array containing the aws_json_node.
 * @param boolean The boolean you want to store in the aws_json_node
 * @return A new boolean aws_json_node
 */
AWS_COMMON_API
struct aws_json_node *aws_json_boolean_new(bool boolean);

/**
 * Creates a new null aws_json_node and returns a pointer to it.
 *
 * Note: You will need to free the memory for the aws_json_node using aws_json_delete on the aws_json_node or
 * on the object/array containing the aws_json_node.
 * @return
 */
AWS_COMMON_API
struct aws_json_node *aws_json_null_new(void);

/**
 * Creates a new object aws_json_node and returns a pointer to it.
 *
 * Note: You will need to free the memory for the aws_json_node using aws_json_delete on the aws_json_node or
 * on the object/array containing the aws_json_node.
 * Deleting this object will also delete any aws_json_nodes it contains.
 * @return
 */
AWS_COMMON_API
struct aws_json_node *aws_json_object_new(void);
// ====================

// ====================
// Value setters and getters

/**
 * Sets the string value of a string aws_json_node.
 * @param node The string aws_json_node.
 * @param string The new string value.
 * @return AWS_OP_SUCCESS if the string was successfully set, otherwise AWS_OP_ERR.
 */
AWS_COMMON_API
int aws_json_string_set(struct aws_json_node *node, char *string);

/**
 * Sets the number value of a number aws_json_node.
 * @param node The number aws_json_node.
 * @param number The new number value.
 * @return AWS_OP_SUCCESS if the number was successfully set, otherwise AWS_OP_ERR.
 */
AWS_COMMON_API
int aws_json_number_set(struct aws_json_node *node, double number);

/**
 * Sets the boolean value of a boolean aws_json_node.
 * @param node The boolean aws_json_node.
 * @param boolean The new boolean value.
 * @return AWS_OP_SUCCESS if the boolean was successfully set, otherwise AWS_OP_ERR.
 */
AWS_COMMON_API
int aws_json_boolean_set(struct aws_json_node *node, bool boolean);

/**
 * Gets the string of a string aws_json_node.
 * @param node The string aws_json_node.
 * @return The string of the string aws_json_node, otherwise NULL.
 */
AWS_COMMON_API
char *aws_json_string_get(struct aws_json_node *node);

/**
 * Gets the number of a number aws_json_node.
 * @param node The number aws_json_node.
 * @return The number of the number aws_json_node, otherwise NULL.
 */
AWS_COMMON_API
double *aws_json_number_get(struct aws_json_node *node);

/**
 * Gets the boolean of a boolean aws_json_node.
 * @param node The boolean aws_json_node.
 * @return The boolean of the boolean aws_json_node, otherwise false.
 */
AWS_COMMON_API
bool aws_json_boolean_get(struct aws_json_node *node);
// ====================

// ====================
// Object API

/**
 * Adds a aws_json_node to a object aws_json_node.
 * @param object The object aws_json_node you want to add a node to.
 * @param key The key to add the aws_json_node at.
 * @param node The aws_json_node you want to add.
 * @return AWS_OP_SUCCESS if adding was successful, otherwise AWS_OP_ERR.
 */
AWS_COMMON_API
int aws_json_object_add(struct aws_json_node *object, char *key, struct aws_json_node *node);

/**
 * Returns the aws_json_node at the given key.
 * @param object The object aws_json_node you want to get the node from.
 * @param key The key that the aws_json_node is at. Is case sensitive.
 * @return The aws_json_node at the given key, otherwise NULL.
 */
AWS_COMMON_API
struct aws_json_node *aws_json_object_get(struct aws_json_node *object, char *key);

/**
 * Returns the aws_json_node at the given case insensitive key.
 * @param object The object aws_json_node you want to get the node from.
 * @param key The key that the aws_json_node is at. Is not case sensitive.
 * @return The aws_json_node at the given key, otherwise NULL.
 */
AWS_COMMON_API
struct aws_json_node *aws_json_object_get_insensitive(struct aws_json_node *object, char *key);

/**
 * Checks if there is a aws_json_node at the given key.
 * @param object The object aws_json_node you want to check a key in.
 * @param key The key that you want to check. Is case sensitive.
 * @return AWS_OP_SUCCESS if a aws_json_node is found, otherwise AWS_OP_ERR.
 */
AWS_COMMON_API
int aws_json_object_has(struct aws_json_node *object, char *key);

/**
 * Removes the aws_json_node at the given key.
 * @param object The object aws_json_node you want to remove a aws_json_node in.
 * @param key The key that the aws_json_node is at. Is case sensitive.
 * @return AWS_OP_SUCCESS if the aws_json_node was removed, otherwise AWS_OP_ERR.
 */
AWS_COMMON_API
int aws_json_object_remove(struct aws_json_node *object, char *key);

/**
 * Removes the aws_json_node from the aws_json_object using a pointer to the aws_json_node.
 * @param object The object aws_json_node you want to remove a aws_json_node in.
 * @param node The aws_json_node you want to remove from the object aws_json_node.
 * @return AWS_OP_SUCCESS if the aws_json_node was removed, otherwise AWS_OP_ERR.
 */
AWS_COMMON_API
int aws_json_object_remove_node(struct aws_json_node *object, struct aws_json_node *node);
// ====================

// ====================
// Array API

/**
 * Adds a aws_json_node to the given array aws_json_node.
 * @param array The array aws_json_node you want to add an aws_json_node to.
 * @param node The aws_json_node you want to add.
 * @return AWS_OP_SUCCESS if adding the aws_json_node was successful, otherwise AWS_OP_ERR.
 */
AWS_COMMON_API
int aws_json_array_add(struct aws_json_node *array, struct aws_json_node *node);

/**
 * Returns the aws_json_node at the given index in the array aws_json_node.
 * @param array The array aws_json_node.
 * @param index The index of the aws_json_node you want to access.
 * @return A pointer to the aws_json_node at the given index in the array, otherwise NULL.
 */
AWS_COMMON_API
struct aws_json_node *aws_json_array_get(struct aws_json_node *array, int index);

/**
 * Returns the number of items in the array aws_json_node.
 * @param array The array aws_json_node.
 * @return The number of items in the array_json_node.
 */
AWS_COMMON_API
int aws_json_array_get_count(struct aws_json_node *array);

/**
 * Returns whether the given aws_json_node is located within the array aws_json_node.
 * @param array The array aws_json_node.
 * @param node The aws_json_node to check for.
 * @return AWS_OP_SUCCESS if the aws_json_node exists in the array, otherwise AWS_OP_ERR.
 */
AWS_COMMON_API
int aws_json_array_has(struct aws_json_node *array, struct aws_json_node *node);

/**
 * Removes the aws_json_node at the given index in the array aws_json_node.
 * @param array The array aws_json_node.
 * @param index The index containing the aws_json_node you want to remove.
 * @return AWS_OP_SUCCESS if the aws_json_node at the index was removed, otherwise AWS_OP_ERR.
 */
AWS_COMMON_API
int aws_json_array_remove(struct aws_json_node *array, int index);

/**
 * Removes the aws_json_node in the array aws_json_node using a pointer to the aws_json_node.
 * @param array The array aws_json_node.
 * @param node The aws_json_node you want to remove from the array.
 * @return AWS_OP_SUCCESS if the aws_json_node was removed from the array, otherwise AWS_OP_ERR.
 */
AWS_COMMON_API
int aws_json_array_remove_node(struct aws_json_node *array, struct aws_json_node *node);
// ====================

// ====================
// Checks

/**
 * Checks if the aws_json_node is a string.
 * @param node The aws_json_node to check.
 * @return AWS_OP_SUCCESS if the aws_json_node is a string aws_json_node, otherwise AWS_OP_ERR.
 */
AWS_COMMON_API
int aws_json_is_string(struct aws_json_node *node);

/**
 * Checks if the aws_json_node is a number.
 * @param node The aws_json_node to check.
 * @return AWS_OP_SUCCESS if the aws_json_node is a number aws_json_node, otherwise AWS_OP_ERR.
 */
AWS_COMMON_API
int aws_json_is_number(struct aws_json_node *node);

/**
 * Checks if the aws_json_node is a array.
 * @param node The aws_json_node to check.
 * @return AWS_OP_SUCCESS if the aws_json_node is a array aws_json_node, otherwise AWS_OP_ERR.
 */
AWS_COMMON_API
int aws_json_is_array(struct aws_json_node *node);

/**
 * Checks if the aws_json_node is a boolean.
 * @param node The aws_json_node to check.
 * @return AWS_OP_SUCCESS if the aws_json_node is a boolean aws_json_node, otherwise AWS_OP_ERR.
 */
AWS_COMMON_API
int aws_json_is_boolean(struct aws_json_node *node);

/**
 * Checks if the aws_json_node is a null aws_json_node.
 * @param node The aws_json_node to check.
 * @return AWS_OP_SUCCESS if the aws_json_node is a null aws_json_node, otherwise AWS_OP_ERR.
 */
AWS_COMMON_API
int aws_json_is_null(struct aws_json_node *node);

/**
 * Checks if the aws_json_node is a object aws_json_node.
 * @param node The aws_json_node to check.
 * @return AWS_OP_SUCCESS if the aws_json_node is a object aws_json_node, otherwise AWS_OP_ERR.
 */
AWS_COMMON_API
int aws_json_is_object(struct aws_json_node *node);
// ====================

// ====================
// Memory Management

/**
 * Initializes the JSON module for use.
 * @param allocator The allocator to use for creating aws_json_node structs.
 */
AWS_COMMON_API
void aws_json_module_init(struct aws_allocator *allocator);

/**
 * Cleans up the JSON module. Should be called when finished using the module.
 */
AWS_COMMON_API
void aws_json_module_cleanup(void);

/**
 * Deletes the aws_json_node from memory. If the aws_json_node is a object or array, it will also delete
 * attached aws_json_nodes as well.
 * @param node The aws_json_node to delete.
 * @return AWS_OP_SUCCESS if the delete was successful, otherwise AWS_OP_ERR.
 */
AWS_COMMON_API
int aws_json_delete(struct aws_json_node *node);

/**
 * Frees the memory of the aws_json_node. Can also be used to free the strings returned
 * by aws_json_to_string functions.
 * @param node The aws_json_node to free.
 * @return AWS_OP_SUCCESS if the free was successful, otherwise AWS_OP_ERR.
 */
AWS_COMMON_API
int aws_json_free(struct aws_json_node *node);
// ====================

// ====================
// Utility

/**
 * Returns an unformatted JSON string representation of the aws_json_node.
 * @param node The aws_json_node to format.
 * @return A string containing the JSON.
 */
AWS_COMMON_API
char *aws_json_to_string(struct aws_json_node *node);

/**
 * Returns a formatted JSON string representation of the aws_json_node.
 * @param node The aws_json_node to format.
 * @return A string containing the JSON.
 */
AWS_COMMON_API
char *aws_json_to_string_formatted(struct aws_json_node *node);

/**
 * Fills the passed in string with a JSON string representation of the aws_json_node.
 * @param node The aws_json_node to format.
 * @param output The string to place the JSON into.
 * @param length The length of the aws_json_node string.
 * @param format A boolean to determine whether to format the result.
 */
AWS_COMMON_API
void aws_json_to_string_preallocated(struct aws_json_node *node, char *output, int length, bool format);

/**
 * Parses the JSON string and returns a aws_json_node containing the root of the JSON.
 * @param string The string containing the JSON.
 * @return The root aws_json_node of the JSON.
 */
AWS_COMMON_API
struct aws_json_node *aws_json_from_string(char *string);

/**
 * Determines if the aws_json_node is a valid aws_json_node.
 * @param node The aws_json_node to check.
 * @return AWS_OP_SUCCESS if the aws_json_node is valid, otherwise AWS_OP_ERR.
 */
AWS_COMMON_API
int aws_json_is_valid(struct aws_json_node *node);
// ====================

#endif // AWS_COMMON_JSON_JSON_H
