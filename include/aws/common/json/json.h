#ifndef AWS_COMMON_JSON_JSON_H
#define AWS_COMMON_JSON_JSON_H

/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */
#include <aws/common/thread.h>

struct aws_json_node;

// ====================
// Create and pass type

/**
 * Creates a new aws_json_node and returns a pointer to it.
 *
 * Note: You will need to free the memory for the aws_json_node using aws_json_node_delete on the aws_json_node or
 * on the object/array containing the aws_json_node.
 * @return A new aws_json_node
 */
struct aws_json_node *aws_json_make_node(void);

/**
 * Creates a new string aws_json_node with the given string and returns a pointer to it.
 *
 * Note: You will need to free the memory for the aws_json_node using aws_json_node_delete on the aws_json_node or
 * on the object/array containing the aws_json_node.
 * @param string The string you want to store in the aws_json_node
 * @return A new string aws_json_node
 */
struct aws_json_node *aws_json_make_node_string(char *string);

/**
 * Creates a new number aws_json_node with the given number and returns a pointer to it.
 *
 * Note: You will need to free the memory for the aws_json_node using aws_json_node_delete on the aws_json_node or
 * on the object/array containing the aws_json_node.
 * @param number The number you want to store in the aws_json_node
 * @return A new number aws_json_node
 */
struct aws_json_node *aws_json_make_node_number(double number);

/**
 * Creates a new array aws_json_node and returns a pointer to it.
 *
 * Note: You will need to free the memory for the aws_json_node using aws_json_node_delete on the aws_json_node or
 * on the object/array containing the aws_json_node.
 * Deleting this array will also delete any aws_json_nodes it contains.
 * @return A new array aws_json_node
 */
struct aws_json_node *aws_json_make_node_array(void);

/**
 * Creates a new boolean aws_json_node with the given boolean and returns a pointer to it.
 *
 * Note: You will need to free the memory for the aws_json_node using aws_json_node_delete on the aws_json_node or
 * on the object/array containing the aws_json_node.
 * @param boolean The boolean you want to store in the aws_json_node
 * @return A new boolean aws_json_node
 */
struct aws_json_node *aws_json_make_node_boolean(bool boolean);

/**
 * Creates a new null aws_json_node and returns a pointer to it.
 *
 * Note: You will need to free the memory for the aws_json_node using aws_json_node_delete on the aws_json_node or
 * on the object/array containing the aws_json_node.
 * @return
 */
struct aws_json_node *aws_json_make_node_null(void);

/**
 * Creates a new object aws_json_node and returns a pointer to it.
 *
 * Note: You will need to free the memory for the aws_json_node using aws_json_node_delete on the aws_json_node or
 * on the object/array containing the aws_json_node.
 * Deleting this object will also delete any aws_json_nodes it contains.
 * @return
 */
struct aws_json_node *aws_json_make_node_object(void);
// ====================

// ====================
// Value setters and getters

/**
 * Sets the string value of a string aws_json_node.
 * @param node The string aws_json_node.
 * @param string The new string value.
 * @return True if the string was successfully set, otherwise false.
 */
bool aws_json_set_string(struct aws_json_node *node, char *string);

/**
 * Sets the number value of a number aws_json_node.
 * @param node The number aws_json_node.
 * @param number The new number value.
 * @return True if the number was successfully set, otherwise false.
 */
bool aws_json_set_number(struct aws_json_node *node, double number);

/**
 * Sets the boolean value of a boolean aws_json_node.
 * @param node The boolean aws_json_node.
 * @param boolean The new boolean value.
 * @return True if the boolean was successfully set, otherwise false.
 */
bool aws_json_set_boolean(struct aws_json_node *node, bool boolean);

/**
 * Gets the string of a string aws_json_node.
 * @param node The string aws_json_node.
 * @return The string of the string aws_json_node, otherwise NULL.
 */
char *aws_json_node_get_string(struct aws_json_node *node);

/**
 * Gets the number of a number aws_json_node.
 * @param node The number aws_json_node.
 * @return The number of the number aws_json_node, otherwise NULL.
 */
double *aws_json_node_get_number(struct aws_json_node *node);

/**
 * Gets the boolean of a boolean aws_json_node.
 * @param node The boolean aws_json_node.
 * @return The boolean of the boolean aws_json_node, otherwise false.
 */
bool aws_json_node_get_boolean(struct aws_json_node *node);
// ====================

// ====================
// Object API

/**
 * Adds a aws_json_node to a object aws_json_node.
 * @param object The object aws_json_node you want to add a node to.
 * @param key The key to add the aws_json_node at.
 * @param node The aws_json_node you want to add.
 * @return True if adding was successful, otherwise false.
 */
bool aws_json_object_add_node(struct aws_json_node *object, char *key, struct aws_json_node *node);

/**
 * Returns the aws_json_node at the given key.
 * @param object The object aws_json_node you want to get the node from.
 * @param key The key that the aws_json_node is at. Is case sensitive.
 * @return The aws_json_node at the given key, otherwise NULL.
 */
struct aws_json_node *aws_json_object_get_node(struct aws_json_node *object, char *key);

/**
 * Returns the aws_json_node at the given case insensitive key.
 * @param object The object aws_json_node you want to get the node from.
 * @param key The key that the aws_json_node is at. Is not case sensitive.
 * @return The aws_json_node at the given key, otherwise NULL.
 */
struct aws_json_node *aws_json_object_get_node_case_insensitive(struct aws_json_node *object, char *key);

/**
 * Checks if there is a aws_json_node at the given key.
 * @param object The object aws_json_node you want to check a key in.
 * @param key The key that you want to check. Is case sensitive.
 * @return True if a aws_json_node is found, otherwise false.
 */
bool aws_json_object_has_node(struct aws_json_node *object, char *key);

/**
 * Deletes the aws_json_node at the given key.
 * @param object The object aws_json_node you want to delete a aws_json_node in.
 * @param key The key that the aws_json_node is at. Is case sensitive.
 * @return True if the aws_json_node was deleted, otherwise false.
 */
bool aws_json_object_delete_node(struct aws_json_node *object, char *key);

/**
 * Deletes the aws_json_node from the aws_json_object using a pointer to the aws_json_node.
 * @param object The object aws_json_node you want to delete a aws_json_node in.
 * @param node The aws_json_node you want to remove from the object aws_json_node.
 * @return True if the aws_json_node was deleted, otherwise false.
 */
bool aws_json_object_delete_node_with_node(struct aws_json_node *object, struct aws_json_node *node);
// ====================

// ====================
// Array API

/**
 * Adds a aws_json_node to the given array aws_json_node.
 * @param array The array aws_json_node you want to add an aws_json_node to.
 * @param node The aws_json_node you want to add.
 * @return True if adding the aws_json_node was successful, otherwise false.
 */
bool aws_json_array_add_node(struct aws_json_node *array, struct aws_json_node *node);

/**
 * Returns the aws_json_node at the given index in the array aws_json_node.
 * @param array The array aws_json_node.
 * @param index The index of the aws_json_node you want to access.
 * @return A pointer to the aws_json_node at the given index in the array, otherwise NULL.
 */
struct aws_json_node *aws_json_array_get_node(struct aws_json_node *array, int index);

/**
 * Returns the number of items in the array aws_json_node.
 * @param array The array aws_json_node.
 * @return The number of items in the array_json_node.
 */
int aws_json_array_get_count(struct aws_json_node *array);

/**
 * Returns whether the given aws_json_node is located within the array aws_json_node.
 * @param array The array aws_json_node.
 * @param node The aws_json_node to check for.
 * @return True if the aws_json_node exists in the array, otherwise false.
 */
bool aws_json_array_has_node(struct aws_json_node *array, struct aws_json_node *node);

/**
 * Deletes the aws_json_node at the given index in the array aws_json_node.
 * @param array The array aws_json_node.
 * @param index The index containing the aws_json_node you want to delete.
 * @return True if the aws_json_node at the index was deleted, otherwise false.
 */
bool aws_json_array_delete_node(struct aws_json_node *array, int index);

/**
 * Deletes the aws_json_node in the array aws_json_node using a pointer to the aws_json_node.
 * @param array The array aws_json_node.
 * @param node The aws_json_node you want to remove from the array.
 * @return True if the aws_json_node was removed from the array, otherwise false.
 */
bool aws_json_array_delete_node_with_node(struct aws_json_node *array, struct aws_json_node *node);
// ====================

// ====================
// Checks

/**
 * Checks if the aws_json_node is a string.
 * @param node The aws_json_node to check.
 * @return True if the aws_json_node is a string aws_json_node, otherwise false.
 */
bool aws_json_node_is_string(struct aws_json_node *node);

/**
 * Checks if the aws_json_node is a number.
 * @param node The aws_json_node to check.
 * @return True if the aws_json_node is a number aws_json_node, otherwise false.
 */
bool aws_json_node_is_number(struct aws_json_node *node);

/**
 * Checks if the aws_json_node is a array.
 * @param node The aws_json_node to check.
 * @return True if the aws_json_node is a array aws_json_node, otherwise false.
 */
bool aws_json_node_is_array(struct aws_json_node *node);

/**
 * Checks if the aws_json_node is a boolean.
 * @param node The aws_json_node to check.
 * @return True if the aws_json_node is a boolean aws_json_node, otherwise false.
 */
bool aws_json_node_is_boolean(struct aws_json_node *node);

/**
 * Checks if the aws_json_node is a null aws_json_node.
 * @param node The aws_json_node to check.
 * @return True if the aws_json_node is a null aws_json_node, otherwise false.
 */
bool aws_json_node_is_null(struct aws_json_node *node);

/**
 * Checks if the aws_json_node is a object aws_json_node.
 * @param node The aws_json_node to check.
 * @return True if the aws_json_node is a object aws_json_node, otherwise false.
 */
bool aws_json_node_is_object(struct aws_json_node *node);
// ====================

// ====================
// Memory Management

/**
 * Initializes the JSON module for use.
 * @param allocator The allocator to use for creating aws_json_node structs.
 */
void aws_json_module_init(struct aws_allocator *allocator);

/**
 * Cleans up the JSON module. Should be called when finished using the module.
 */
void aws_json_module_cleanup(void);

/**
 * Deletes the aws_json_node from memory. If the aws_json_node is a object or array, it will also delete
 * attached aws_json_nodes as well.
 * @param node The aws_json_node to delete.
 * @return True if the delete was successful, otherwise false.
 */
bool aws_json_node_delete(struct aws_json_node *node);

/**
 * Frees the memory of the aws_json_node. Can also be used to free the strings returned
 * by aws_json_node_to_string functions.
 * @param node The aws_json_node to free.
 * @return True if the free was successful, otherwise false.
 */
bool aws_json_node_free(struct aws_json_node *node);
// ====================

// ====================
// Utility

/**
 * Returns an unformatted JSON string representation of the aws_json_node.
 * @param node The aws_json_node to format.
 * @return A string containing the JSON.
 */
char *aws_json_node_to_string(struct aws_json_node *node);

/**
 * Returns a formatted JSON string representation of the aws_json_node.
 * @param node The aws_json_node to format.
 * @return A string containing the JSON.
 */
char *aws_json_node_to_string_formatted(struct aws_json_node *node);

/**
 * Fills the passed in string with a JSON string representation of the aws_json_node.
 * @param node The aws_json_node to format.
 * @param output The string to place the JSON into.
 * @param length The length of the aws_json_node string.
 * @param format A boolean to determine whether to format the result.
 */
void aws_json_print_to_string_preallocated(struct aws_json_node *node, char *output, int length, bool format);

/**
 * Parses the JSON string and returns a aws_json_node containing the root of the JSON.
 * @param string The string containing the JSON.
 * @return The root aws_json_node of the JSON.
 */
struct aws_json_node *aws_json_node_from_string(char *string);

/**
 * Determines if the aws_json_node is a valid aws_json_node.
 * @param node The aws_json_node to check.
 * @return True if the aws_json_node is valid, otherwise false.
 */
bool aws_json_node_is_valid(struct aws_json_node *node);
// ====================

#endif // AWS_COMMON_JSON_JSON_H
