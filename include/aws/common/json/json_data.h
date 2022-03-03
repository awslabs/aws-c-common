#ifndef AWS_IOT_DEVICE_SDK_CPP_V2_JSON_DATA_H
#define AWS_IOT_DEVICE_SDK_CPP_V2_JSON_DATA_H

/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/common/thread.h>

enum aws_json_node_type {
    json_type_string,
    json_type_number,
    json_type_array,
    json_type_boolean,
    json_type_null,
    json_type_object,
};

struct aws_json_node {
    enum aws_json_node_type type;
    void *data;
    char* key;
    struct aws_json_node *next;
};

struct aws_json_node *aws_json_make_node(char* name);
struct aws_json_node *aws_json_make_node_string(char* name, char *string);
struct aws_json_node *aws_json_make_node_number(char* name, double number);
struct aws_json_node *aws_json_make_node_array(char* name);
struct aws_json_node *aws_json_make_node_boolean(char* name, bool boolean);
struct aws_json_node *aws_json_make_node_null(char* name);
struct aws_json_node *aws_json_make_node_object(char* name, struct aws_json_node *node);

bool aws_json_set_value(struct aws_json_node *node, enum aws_json_node_type type, void *data);

bool aws_json_node_is_string(struct aws_json_node *node);
bool aws_json_node_is_number(struct aws_json_node *node);
bool aws_json_node_is_array(struct aws_json_node *node);
bool aws_json_node_is_boolean(struct aws_json_node *node);
bool aws_json_node_is_null(struct aws_json_node *node);
bool aws_json_node_is_object(struct aws_json_node *node);

char* aws_json_node_get_string(struct aws_json_node *node);
double *aws_json_node_get_number(struct aws_json_node *node);
struct aws_json_node *aws_json_node_get_object(struct aws_json_node *node);
struct aws_json_node *aws_json_node_get_array(struct aws_json_node *node);
bool *aws_json_node_get_boolean(struct aws_json_node *node);

bool aws_json_node_delete(struct aws_json_node *node);

bool aws_json_add_node_to_array(struct aws_json_node *array, struct aws_json_node *node_to_add);
bool aws_json_node_add_to_array(struct aws_json_node *array, struct aws_json_node *node_to_add, int index);
bool aws_json_delete_node_from_array(struct aws_json_node *array, int index);
bool aws_json_delete_node_from_array_with_node(struct aws_json_node *array, struct aws_json_node *node_to_delete);
struct aws_json_node *aws_json_get_node_from_array(struct aws_json_node *array, int index);

bool aws_json_add_node_to_object(struct aws_json_node *array, struct aws_json_node *node_to_add);
bool aws_json_delete_node_from_object(struct aws_json_node *array, struct aws_json_node *node_to_remove);
bool aws_json_delete_node_from_object_string(struct aws_json_node *array, char* string);
struct aws_json_node *aws_json_get_node_from_object(struct aws_json_node *array, char* string);

#endif // AWS_IOT_DEVICE_SDK_CPP_V2_JSON_DATA_H
