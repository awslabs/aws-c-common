#ifndef AWS_COMMON_JSON_JSON_H
#define AWS_COMMON_JSON_JSON_H

/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */
#include <aws/common/thread.h>

// ====================
// Create and pass type
void *aws_json_make_node(void);
void *aws_json_make_node_string(char *string);
void *aws_json_make_node_number(double number);
void *aws_json_make_node_array(void);
void *aws_json_make_node_boolean(bool boolean);
void *aws_json_make_node_null(void);
void *aws_json_make_node_object(void);
// ====================

// ====================
// Value setters and getters
bool aws_json_set_string(void *node, char *string);
bool aws_json_set_number(void *node, double number);
bool aws_json_set_boolean(void *node, bool boolean);

char *aws_json_node_get_string(void *node);
double *aws_json_node_get_number(void *node);
bool aws_json_node_get_boolean(void *node);
// ====================

// ====================
// Object API
bool aws_json_object_add_node(void *object, char *key, void *node);
void *aws_json_object_get_node(void *object, char *key);
void *aws_json_object_get_node_case_insensitive(void *object, char *key);
bool aws_json_object_has_node(void *object, char *key);
bool aws_json_object_delete_node(void *object, char *key);
bool aws_json_object_delete_node_with_node(void *object, void *node);
// ====================

// ====================
// Array API
bool aws_json_array_add_node(void *array, void *node);
void *aws_json_array_get_node(void *array, int index);
int aws_json_array_get_count(void *array);
bool aws_json_array_has_node(void *array, void *node);
bool aws_json_array_delete_node(void *array, int index);
bool aws_json_array_delete_node_with_node(void *array, void *node);
// ====================

// ====================
// Checks
bool aws_json_node_is_string(void *node);
bool aws_json_node_is_number(void *node);
bool aws_json_node_is_array(void *node);
bool aws_json_node_is_boolean(void *node);
bool aws_json_node_is_null(void *node);
bool aws_json_node_is_object(void *node);
// ====================

// ====================
// Memory Management
void aws_json_module_init(struct aws_allocator *allocator);
void aws_json_module_cleanup(void);
bool aws_json_node_delete(void *node);
bool aws_json_node_free(void *node);
// ====================

// ====================
// Utility
char* aws_json_node_to_string(void *node);
char* aws_json_node_to_string_formatted(void *node);
void aws_json_print_to_string_preallocated(void *node, char* output, int length, bool format);
void *aws_json_node_from_string(char* string);
bool aws_json_node_is_valid(void *node);
// ====================

#endif // AWS_COMMON_JSON_JSON_H
