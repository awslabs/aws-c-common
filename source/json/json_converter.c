/**
* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
* SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/common/json/json_converter.h>
#include <aws/common/json/external/cJSON.h>


struct aws_allocator *aws_json_converter_module_allocator = NULL;
bool aws_json_converter_module_initialized = false;

void *aws_cJSON_alloc(size_t sz) {
    return aws_mem_acquire(aws_json_converter_module_allocator, sz);
}

void aws_cJSON_free(void *ptr) {
    aws_mem_release(aws_json_converter_module_allocator, ptr);
}

void aws_json_converter_init(struct aws_allocator *allocator) {
    if (!aws_json_converter_module_initialized) {
        aws_json_converter_module_allocator = allocator;
        struct cJSON_Hooks allocation_hooks = {.malloc_fn = aws_cJSON_alloc, .free_fn = aws_cJSON_free};
        cJSON_InitHooks(&allocation_hooks);
        aws_json_converter_module_initialized = true;
    }
}

void aws_json_converter_clean_up() {
    if (aws_json_converter_module_initialized) {
        aws_json_converter_module_allocator = NULL;
        aws_json_converter_module_initialized = false;
    }
}


static void convert_cJSON_to_aws_json_single(struct aws_json_node* parent, struct cJSON *node) {
    if (node == NULL) {
        return;
    }

    struct aws_json_node *aws_node = NULL;
    if (cJSON_IsNull(node)) {
        aws_node = aws_json_make_node_null(node->string);
    } else if (cJSON_IsString(node)) {
        aws_node = aws_json_make_node_string(node->string, cJSON_GetStringValue(node));
    } else if (cJSON_IsNumber(node)) {
        aws_node = aws_json_make_node_number(node->string, node->valuedouble);
    } else if (cJSON_IsBool(node)) {
        if (node->type == cJSON_True) {
            aws_node = aws_json_make_node_boolean(node->string, true);
        } else {
            aws_node = aws_json_make_node_boolean(node->string, false);
        }
    } else if (cJSON_IsArray(node)) {
        // NOT 100% sure this will work...
        aws_node = aws_json_make_node_array(node->string);
        int array_size = cJSON_GetArraySize(node);
        for (int i = 0; i < array_size; i++) {
            convert_cJSON_to_aws_json_single(aws_node, cJSON_GetArrayItem(node, i));
        }
    } else if (cJSON_IsObject(node)) {
        // NOT 100% sure this will work...
        aws_node = aws_json_make_node_object(node->string, NULL);
        cJSON *child = node->next;
        while (child != NULL) {
            convert_cJSON_to_aws_json_single(aws_node, child);
            child = child->next;
        }
    }

    if (parent->type == json_type_object) {
        aws_json_add_node_to_object(parent, aws_node);
    } else if (parent->type == json_type_array) {
        aws_json_add_node_to_array(parent, aws_node);
    } else {
        printf("Error - cannot add JSON node to anything! Deleting node...");
        aws_json_node_delete(aws_node);
    }
}
struct aws_json_node *aws_parse_json_from_string(char* string) {
    struct cJSON *node = cJSON_Parse(string);
    struct aws_json_node *root = aws_json_make_node_object("", NULL);
    convert_cJSON_to_aws_json_single(root, node);
    cJSON_Delete(node);
    return root;
}


static cJSON *convert_aws_json_to_cJSON_single(struct cJSON *parent, struct aws_json_node *node) {
    if (node == NULL) {
        return NULL;
    }

    struct cJSON *node_csjon = NULL;
    if (node->data == NULL) {
        node_csjon = cJSON_CreateNull();
    } else {
        if (node->type == json_type_null) {
            node_csjon = cJSON_CreateNull();
        } else if (node->type == json_type_string) {
            node_csjon = cJSON_CreateString(node->data);
        } else if (node->type == json_type_number) {
            node_csjon = cJSON_CreateNumber(*(double*)node->data);
        } else if (node->type == json_type_boolean) {
            node_csjon = cJSON_CreateBool(*(bool*)node->data);
        } else if (node->type == json_type_array) {
            node_csjon = cJSON_CreateArray();

            // Iterate through array
            struct aws_json_node *child = node->next;
            struct cJSON *child_csjon = NULL;
            while (child != NULL) {
                child_csjon = convert_aws_json_to_cJSON_single(node_csjon, child);
                child = child->next;
                cJSON_AddItemToArray(node_csjon, child_csjon);
            }
        } else if (node->type == json_type_object) {
            node_csjon = cJSON_CreateObject();

            // Iterate through object
            struct aws_json_node *child = node->next;
            struct cJSON *child_csjon = NULL;
            while (child != NULL) {
                child_csjon = convert_aws_json_to_cJSON_single(node_csjon, child);
                child = child->next;
                cJSON_AddItemToObject(node_csjon, child->key, child_csjon);
            }
        }
    }

    // If it is not an array or object, then add it
    if (cJSON_IsArray(parent) == false && cJSON_IsObject(parent) == false) {
        cJSON_AddItemToObject(parent, node->key, node_csjon);
    }

    return node_csjon;
}

char *aws_convert_json_to_string(struct aws_json_node *node) {
    struct cJSON *root = cJSON_CreateObject();
    convert_aws_json_to_cJSON_single(root, node);

    char* return_value = cJSON_PrintUnformatted(root);
    cJSON_Delete(root);
    return return_value;
}
