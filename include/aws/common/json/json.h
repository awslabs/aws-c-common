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
struct aws_json_node *aws_json_make_node(void);
struct aws_json_node *aws_json_make_node_string(char *string);
struct aws_json_node *aws_json_make_node_number(double number);
struct aws_json_node *aws_json_make_node_array(void);
struct aws_json_node *aws_json_make_node_boolean(bool boolean);
struct aws_json_node *aws_json_make_node_null(void);
struct aws_json_node *aws_json_make_node_object(void);
// ====================

// ====================
// Value setters and getters
bool aws_json_set_string(struct aws_json_node *node, char *string);
bool aws_json_set_number(struct aws_json_node *node, double number);
bool aws_json_set_boolean(struct aws_json_node *node, bool boolean);

char *aws_json_node_get_string(struct aws_json_node *node);
double *aws_json_node_get_number(struct aws_json_node *node);
bool aws_json_node_get_boolean(struct aws_json_node *node);
// ====================

// ====================
// Object API
bool aws_json_object_add_node(struct aws_json_node *object, char *key, struct aws_json_node *node);
struct aws_json_node *aws_json_object_get_node(struct aws_json_node *object, char *key);
struct aws_json_node *aws_json_object_get_node_case_insensitive(struct aws_json_node *object, char *key);
bool aws_json_object_has_node(struct aws_json_node *object, char *key);
bool aws_json_object_delete_node(struct aws_json_node *object, char *key);
bool aws_json_object_delete_node_with_node(struct aws_json_node *object, struct aws_json_node *node);
// ====================

// ====================
// Array API
bool aws_json_array_add_node(struct aws_json_node *array, struct aws_json_node *node);
struct aws_json_node *aws_json_array_get_node(struct aws_json_node *array, int index);
int aws_json_array_get_count(struct aws_json_node *array);
bool aws_json_array_has_node(struct aws_json_node *array, struct aws_json_node *node);
bool aws_json_array_delete_node(struct aws_json_node *array, int index);
bool aws_json_array_delete_node_with_node(struct aws_json_node *array, struct aws_json_node *node);
// ====================

// ====================
// Checks
bool aws_json_node_is_string(struct aws_json_node *node);
bool aws_json_node_is_number(struct aws_json_node *node);
bool aws_json_node_is_array(struct aws_json_node *node);
bool aws_json_node_is_boolean(struct aws_json_node *node);
bool aws_json_node_is_null(struct aws_json_node *node);
bool aws_json_node_is_object(struct aws_json_node *node);
// ====================

// ====================
// Memory Management
void aws_json_module_init(struct aws_allocator *allocator);
void aws_json_module_cleanup(void);
bool aws_json_node_delete(struct aws_json_node *node);
bool aws_json_node_free(struct aws_json_node *node);
// ====================

// ====================
// Utility
char *aws_json_node_to_string(struct aws_json_node *node);
char *aws_json_node_to_string_formatted(struct aws_json_node *node);
void aws_json_print_to_string_preallocated(struct aws_json_node *node, char *output, int length, bool format);
struct aws_json_node *aws_json_node_from_string(char *string);
bool aws_json_node_is_valid(struct aws_json_node *node);
// ====================

#endif // AWS_COMMON_JSON_JSON_H
