/**
* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
* SPDX-License-Identifier: Apache-2.0.
*/

#include <aws/common/json/json_data.h>

struct aws_json_node *aws_json_make_node(char* key_name) {
    // TODO - replace with AWS new/delete. For now, use default C just to get something working.
    // TODO - this whole function really needs to be rewritten... Will get to later.
    struct aws_json_node *return_val = malloc(sizeof *return_val);
    if (!return_val) {
        printf("Could not allocate aws_json_node");
        return NULL;
    }
    return_val->type = json_type_null;
    return_val->key = key_name;
    return return_val;
}
struct aws_json_node *aws_json_make_node_string(char* key_name, char *string) {
    struct aws_json_node *return_value = aws_json_make_node(key_name);
    return_value->type = json_type_string;
    return_value->data = string;
    return return_value;
}
struct aws_json_node *aws_json_make_node_number(char* key_name, double number) {
    struct aws_json_node *return_value = aws_json_make_node(key_name);
    return_value->type = json_type_number;
    return_value->data = &number;
    return return_value;
}
struct aws_json_node *aws_json_make_node_array(char* key_name) {
    struct aws_json_node *return_value = aws_json_make_node(key_name);
    return_value->type = json_type_array;
    return return_value;
}
struct aws_json_node *aws_json_make_node_boolean(char* key_name, bool boolean) {
    struct aws_json_node *return_value = aws_json_make_node(key_name);
    return_value->type = json_type_boolean;
    return_value->data = &boolean;
    return return_value;
}
struct aws_json_node *aws_json_make_node_null(char* key_name) {
    return aws_json_make_node(key_name);
}
struct aws_json_node *aws_json_make_node_object(char* key_name, struct aws_json_node *node) {
    struct aws_json_node *return_value = aws_json_make_node(key_name);
    return_value->type = json_type_object;
    return_value->data = node;
    return return_value;
}

bool aws_json_set_value(struct aws_json_node *node, enum aws_json_node_type type, void* data) {
    if (node->data != NULL) {
        return false;
    }

    // TODO - add type checking or remove use of void* with a different struct or something...

    node->type = type;
    node->data = data;
    return true;
}

bool aws_json_node_is_string(struct aws_json_node *node) {
    if (node == NULL) {
        return false;
    }
    return (node->type == json_type_string);
}
bool aws_json_node_is_number(struct aws_json_node *node) {
    if (node == NULL) {
        return false;
    }
    return (node->type == json_type_number);
}
bool aws_json_node_is_array(struct aws_json_node *node) {
    if (node == NULL) {
        return false;
    }
    return (node->type == json_type_array);
}
bool aws_json_node_is_boolean(struct aws_json_node *node) {
    if (node == NULL) {
        return false;
    }
    return (node->type == json_type_boolean);
}
bool aws_json_node_is_null(struct aws_json_node *node) {
    if (node == NULL) {
        return false;
    }
    return (node->type == json_type_null);
}
bool aws_json_node_is_object(struct aws_json_node *node) {
    if (node == NULL) {
        return false;
    }
    return (node->type == json_type_object);
}

char* aws_json_node_get_string(struct aws_json_node *node) {
    if (node == NULL || node->data == NULL || node->type != json_type_string) {
        return NULL;
    }
    return node->data;
}
double *aws_json_node_get_number(struct aws_json_node *node) {
    if (node == NULL || node->data == NULL || node->type != json_type_number) {
        return 0;
    }
    return node->data;
}
struct aws_json_node *aws_json_node_get_array(struct aws_json_node *node) {
    if (node == NULL || node->data == NULL || node->type != json_type_array) {
        return 0;
    }
    return node->data;
}
struct aws_json_node *aws_json_node_get_object(struct aws_json_node *node) {
    if (node == NULL || node->data == NULL || node->type != json_type_array) {
        return 0;
    }
    return node->data;
}
bool *aws_json_node_get_boolean(struct aws_json_node *node) {
    if (node == NULL || node->data == NULL || node->type != json_type_boolean) {
        return 0;
    }
    return node->data;
}

static void aws_json_node_delete_children(struct aws_json_node *node) {
    // TODO - replace with AWS new/delete. For now, use default C just to get something working.
    // TODO - this whole function really needs to be rewritten... Will get to later.
    if (node != NULL) {
        // If an array or object, then delete the children first BEFORE deleting this node
        if (node->type == json_type_array) {
            aws_json_node_delete_children(node->data);
        }
        // If we are in an array, delete the next element in the array
        if (node->next != NULL) {
            aws_json_node_delete_children(node->next);
        }

        if (node->data != NULL) {
            free(node->data);
        }
        free(node);
    }
}
bool aws_json_node_delete(struct aws_json_node *node) {
    // TODO - replace with AWS new/delete. For now, use default C just to get something working.
    // TODO - this whole function really needs to be rewritten... Will get to later.
    if (node != NULL) {
        if (node->data != NULL) {
            // If an array or object, then delete the children first BEFORE deleting this node
            if (node->type == json_type_array) {
                aws_json_node_delete_children(node->data);
            }
        }

        if (node->data != NULL) {
            free(node->data);
        }
        free(node);
        return true;
    }
    return false;
}

static void aws_json_add_node_to_array_traverse_list(struct aws_json_node *node_in_list, struct aws_json_node *node_to_add) {
    if (node_in_list->next != NULL) {
        aws_json_add_node_to_array_traverse_list(node_in_list->next, node_to_add);
    } else {
        node_in_list->next = node_to_add;
    }
}
bool aws_json_add_node_to_array(struct aws_json_node *array, struct aws_json_node *node_to_add) {
    if (array != NULL) {
        if (array->type == json_type_array) {
            if (array->data == NULL) {
                array->data = node_to_add;
                return true;
            }
            else {
                aws_json_add_node_to_array_traverse_list(array->data, node_to_add);
            }
        }
    }
    return false;
}

static bool aws_json_node_add_to_array_traverse_list(struct aws_json_node *node_in_list,
                                                      struct aws_json_node *node_to_add,
                                                      int desired_index,
                                                      int index_count) {
    if (node_in_list == NULL) {
        return false;
    }
    if (index_count == desired_index) {
        struct aws_json_node *tmp = node_in_list->next;
        node_in_list->next = node_to_add;
        node_to_add->next = tmp;
        return true;
    } else {
        if (node_in_list->next == NULL) {
            if (index_count + 1 == desired_index) {
                node_in_list->next = node_to_add;
                return true;
            } else {
                return false;
            }
        } else {
            return aws_json_node_add_to_array_traverse_list(node_in_list->next, node_to_add, desired_index, index_count+1);
        }
    }
}
bool aws_json_node_add_to_array(struct aws_json_node *array, struct aws_json_node *node_to_add, int index) {
    if (array == NULL || array->type != json_type_array) {
        return false;
    }
    if (node_to_add == NULL || index < 0) {
        return false;
    }
    if (array->data == NULL) {
        array->data = node_to_add;
        return true;
    }
    else {
        return aws_json_node_add_to_array_traverse_list(array->data, node_to_add, index, 0);
    }
}

static bool aws_json_delete_node_from_array_traverse_list(struct aws_json_node *node_in_list,
                                                                        int desired_index,
                                                                        int index_count) {
    if (node_in_list == NULL) {
        return false;
    }
    if (index_count == desired_index) {
        aws_json_node_delete(node_in_list);
        return true;
    } else {
        if (node_in_list->next == NULL) {
            return false;
        } else {
            return aws_json_delete_node_from_array_traverse_list(node_in_list->next, desired_index, index_count+1);
        }
    }
}
bool aws_json_delete_node_from_array(struct aws_json_node *array, int index) {
    if (array == NULL || array->type != json_type_array || array->data == NULL || index < 0) {
        return NULL;
    }
    return aws_json_delete_node_from_array_traverse_list(array->data, index, 0);
}

static bool aws_json_delete_node_from_array_with_node_traverse_list(struct aws_json_node *node_in_list,
                                                                    struct aws_json_node *desired_node) {
    if (node_in_list == NULL) {
        return false;
    }
    if (node_in_list == desired_node) {
        aws_json_node_delete(node_in_list);
        return true;
    } else {
        if (node_in_list->next == NULL) {
            return false;
        } else {
            return aws_json_delete_node_from_array_with_node_traverse_list(node_in_list->next, desired_node);
        }
    }
}
bool aws_json_delete_node_from_array_with_node(struct aws_json_node *array, struct aws_json_node *node_to_delete) {
    if (array == NULL || array->type != json_type_array || array->data == NULL || node_to_delete == NULL) {
        return false;
    }
    return aws_json_delete_node_from_array_with_node_traverse_list(array->data, node_to_delete);
}

static struct aws_json_node *aws_json_get_node_from_array_traverse_list(struct aws_json_node *node_in_list,
                                                                        int desired_index,
                                                                        int index_count) {
    if (node_in_list == NULL) {
        return NULL;
    }
    if (index_count == desired_index) {
        return node_in_list;
    } else {
        if (node_in_list->next == NULL) {
            return NULL;
        } else {
            return aws_json_get_node_from_array_traverse_list(node_in_list->next, desired_index, index_count+1);
        }
    }
}
struct aws_json_node *aws_json_get_node_from_array(struct aws_json_node *array, int index) {
    if (array == NULL || array->type != json_type_array || array->data == NULL || index < 0) {
        return NULL;
    }
    return aws_json_get_node_from_array_traverse_list(array->data, index, 0);
}

bool aws_json_add_node_to_object(struct aws_json_node *array, struct aws_json_node *node_to_add) {
    if (array == NULL || array->type != json_type_object) {
        return false;
    }
    if (node_to_add == NULL) {
        return false;
    }

    if (array->data == NULL) {
        array->data = node_to_add;
        return true;
    }
    else {
        // We can reuse this function, as arrays in aws_json are the same as objects, they are just parsed differently.
        aws_json_add_node_to_array_traverse_list(array->data, node_to_add);
        return true;
    }
}

bool aws_json_delete_node_from_object(struct aws_json_node *array, struct aws_json_node *node_to_remove) {
    if (array == NULL || array->type != json_type_object || array->data == NULL) {
        return false;
    }
    // We can reuse this function, as arrays in aws_json are the same as objects, they are just parsed differently.
    return aws_json_delete_node_from_array_with_node_traverse_list(array, node_to_remove);
}

static bool aws_json_delete_node_from_object_string_traverse_list(struct aws_json_node *node_in_list,
                                                                  char* string) {
    if (node_in_list == NULL) {
        return false;
    }
    if (node_in_list->key == string) {
        aws_json_node_delete(node_in_list);
        return true;
    }
    else {
        if (node_in_list->next == NULL) {
            return false;
        } else {
            return aws_json_delete_node_from_object_string_traverse_list(node_in_list->next, string);
        }
    }
}
bool aws_json_delete_node_from_object_string(struct aws_json_node *array, char* string) {
    if (array == NULL || array->type != json_type_object || array->data == NULL) {
        return false;
    }
    return aws_json_delete_node_from_object_string_traverse_list(array, string);
}

static struct aws_json_node *aws_json_get_node_from_object_traverse_list(struct aws_json_node *node_in_list,
                                                        char* string) {
    if (node_in_list == NULL) {
        return NULL;
    }
    if (node_in_list->key == string) {
        return node_in_list;
    }
    else {
        if (node_in_list->next == NULL) {
            return NULL;
        } else {
            return aws_json_get_node_from_object_traverse_list(node_in_list->next, string);
        }
    }
}
struct aws_json_node *aws_json_get_node_from_object(struct aws_json_node *array, char* string) {
    if (array == NULL || array->type != json_type_object || array->data == NULL) {
        return NULL;
    }
    return aws_json_get_node_from_object_traverse_list(array, string);
}
