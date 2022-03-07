/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/common/json/json.h>
#include <aws/common/json/external/cJSON.h>

void *aws_json_make_node(void) {
    return (void*)cJSON_CreateObject();
}
void *aws_json_make_node_string(char *string) {
    return (void*)cJSON_CreateString(string);
}
void *aws_json_make_node_number(double number) {
    return (void*)cJSON_CreateNumber(number);
}
void *aws_json_make_node_array(void) {
    return (void*)cJSON_CreateArray();
}
void *aws_json_make_node_boolean(bool boolean) {
    return (void*)cJSON_CreateBool(boolean);
}
void *aws_json_make_node_null(void) {
    return (void*)cJSON_CreateNull();
}
void *aws_json_make_node_object(void) {
    return aws_json_make_node();
}

bool aws_json_set_string(void *node, char *string) {
    cJSON *cjson = (cJSON*)node;
    if (cJSON_IsString(cjson)) {
        cjson->valuestring = string;
        return true;
    }
    return false;
}
bool aws_json_set_number(void *node, double number) {
    cJSON *cjson = (cJSON*)node;
    if (cJSON_IsNumber(cjson)) {
        cJSON_SetNumberHelper(cjson, number);
        return true;
    }
    return false;
}
bool aws_json_set_boolean(void *node, bool boolean) {
    cJSON *cjson = (cJSON*)node;
    if (cJSON_IsNumber(cjson)) {
        if (boolean) {
            cjson->type = cJSON_True;
        } else {
            cjson->type = cJSON_False;
        }
        return true;
    }
    return false;
}

char *aws_json_node_get_string(void *node) {
    cJSON *cjson = (cJSON*)node;
    if (cJSON_IsString(cjson)) {
        return cJSON_GetStringValue(cjson);
    }
    return NULL;
}
double *aws_json_node_get_number(void *node) {
    cJSON *cjson = (cJSON*)node;
    if (cJSON_IsNumber(cjson)) {
        return &cjson->valuedouble;
    }
    return NULL;
}
bool aws_json_node_get_boolean(void *node) {
    cJSON *cjson = (cJSON*)node;
    if (cJSON_IsBool(cjson)) {
        if (cjson->type == cJSON_True) {
            return true;
        } else {
            return false;
        }
    }
    return NULL;
}

bool aws_json_object_add_node(void *object, char *key, void *node) {
    cJSON *cjson = (cJSON*)object;
    if (cJSON_IsObject(cjson)) {
        cJSON *cjson_node = (cJSON*)node;
        if (cJSON_HasObjectItem(cjson, key) == false) {
            cJSON_AddItemToObject(cjson, key, cjson_node);
            return true;
        }
        return false;
    }
    return false;
}
void *aws_json_object_get_node(void *object, char *key) {
    cJSON *cjson = (cJSON*)object;
    if (cJSON_IsObject(cjson)) {
        return cJSON_GetObjectItem(cjson, key);
    }
    return NULL;
}
void *aws_json_object_get_node_case_insensitive(void *object, char *key) {
    cJSON *cjson = (cJSON*)object;
    if (cJSON_IsObject(cjson)) {
        return cJSON_GetObjectItemCaseSensitive(cjson, key);
    }
    return NULL;
}
bool aws_json_object_has_node(void *object, char *key) {
    cJSON *cjson = (cJSON*)object;
    if (cJSON_IsObject(cjson)) {
        return cJSON_HasObjectItem(cjson, key);
    }
    return false;
}
bool aws_json_object_delete_node(void *object, char *key) {
    cJSON *cjson = (cJSON*)object;
    if (cJSON_IsObject(cjson)) {
        if (cJSON_HasObjectItem(cjson, key)) {
            cJSON_DeleteItemFromObject(cjson, key);
            return true;
        }
    }
    return false;
}
bool aws_json_object_delete_node_with_node(void *object, void *node) {
    cJSON *cjson = (cJSON*)object;
    if (cJSON_IsObject(cjson)) {
        cJSON *cjson_node = (cJSON*)node;
        if (cjson_node->string != NULL) {
            if (cJSON_HasObjectItem(cjson, cjson_node->string)) {
                cJSON_DeleteItemFromObject(cjson, cjson_node->string);
                return true;
            }
        }
    }
    return false;
}

bool aws_json_array_add_node(void *array, void *node) {
    cJSON *cjson = (cJSON*)array;
    if (cJSON_IsArray(cjson)) {
        cJSON *cjson_node = (cJSON*)node;
        cJSON_AddItemToArray(cjson, cjson_node);
        return true;
    }
    return false;
}
void *aws_json_array_get_node(void *array, int index) {
    cJSON *cjson = (cJSON*)array;
    if (cJSON_IsArray(cjson)) {
        return (void*)cJSON_GetArrayItem(cjson, index);
    }
    return NULL;
}
int aws_json_array_get_count(void *array) {
    cJSON *cjson = (cJSON*)array;
    if (cJSON_IsArray(cjson)) {
        return cJSON_GetArraySize(cjson);
    }
    return 0;
}
bool aws_json_array_has_node(void *array, void *node) {
    cJSON *cjson = (cJSON*)array;
    if (cJSON_IsArray(cjson)) {
        cJSON *cjson_node = (cJSON*)node;

        cJSON *array_child = cjson->child;
        while (array_child != NULL) {
            if (array_child == cjson_node) {
                return true;
            }
            array_child = array_child->next;
        }

        return false;
    }
    return false;
}
bool aws_json_array_delete_node(void *array, int index) {
    cJSON *cjson = (cJSON*)array;
    if (cJSON_IsArray(cjson)) {
        if (index > 0 && index < cJSON_GetArraySize(cjson)) {
            cJSON_DeleteItemFromArray(cjson, index);
            return true;
        }
    }
    return false;
}
bool aws_json_array_delete_node_with_node(void *array, void *node) {
    cJSON *cjson = (cJSON*)array;
    if (cJSON_IsArray(cjson)) {
        cJSON *cjson_node = (cJSON*)node;
        int index = 0;

        cJSON *array_child = cjson->child;
        while (array_child != NULL) {
            if (array_child == cjson_node) {
                cJSON_DeleteItemFromArray(cjson, index);
                return true;
            }
            array_child = array_child->next;
            index += 1;
        }
        return false;
    }
    return false;
}

bool aws_json_node_is_string(void *node) {
    cJSON *cjson = (cJSON*)node;
    return cJSON_IsString(cjson);
}
bool aws_json_node_is_number(void *node) {
    cJSON *cjson = (cJSON*)node;
    return cJSON_IsNumber(cjson);
}
bool aws_json_node_is_array(void *node) {
    cJSON *cjson = (cJSON*)node;
    return cJSON_IsArray(cjson);
}
bool aws_json_node_is_boolean(void *node) {
    cJSON *cjson = (cJSON*)node;
    return cJSON_IsBool(cjson);
}
bool aws_json_node_is_null(void *node) {
    cJSON *cjson = (cJSON*)node;
    return cJSON_IsNull(cjson);
}
bool aws_json_node_is_object(void *node) {
    cJSON *cjson = (cJSON*)node;
    return cJSON_IsObject(cjson);
}

static struct aws_allocator *s_aws_json_module_allocator = NULL;
static bool s_aws_json_module_initialized = false;

void *aws_cJSON_alloc(size_t sz) {
    return aws_mem_acquire(s_aws_json_module_allocator, sz);
}

void aws_cJSON_free(void *ptr) {
    aws_mem_release(s_aws_json_module_allocator, ptr);
}

void aws_json_module_init(struct aws_allocator *allocator) {
    if (!s_aws_json_module_initialized) {
        s_aws_json_module_allocator = allocator;
        struct cJSON_Hooks allocation_hooks = {.malloc_fn = aws_cJSON_alloc, .free_fn = aws_cJSON_free};
        cJSON_InitHooks(&allocation_hooks);
        s_aws_json_module_initialized = true;
    }
}
void aws_json_module_cleanup(void) {
    if (s_aws_json_module_initialized) {
        s_aws_json_module_allocator = NULL;
        s_aws_json_module_initialized = false;
    }
}
bool aws_json_node_delete(void *node) {
    cJSON *cjson = (cJSON*)node;
    if (cjson != NULL) {
        cJSON_Delete(cjson);
        return true;
    }
    return false;
}
bool aws_json_node_free(void *node) {
    cJSON *cjson = (cJSON*)node;
    if (cjson != NULL) {
        cJSON_free(cjson);
        return true;
    }
    return false;
}

char* aws_json_node_to_string(void *node) {
    cJSON *cjson = (cJSON*)node;
    if (node != NULL) {
        return cJSON_PrintUnformatted(cjson);
    }
    return NULL;
}
char* aws_json_node_to_string_formatted(void *node) {
    cJSON *cjson = (cJSON*)node;
    if (node != NULL) {
        return cJSON_Print(cjson);
    }
    return NULL;
}
void aws_json_print_to_string_preallocated(void *node, char* output, int length, bool format) {
    cJSON *cjson = (cJSON*)node;
    if (node != NULL) {
        cJSON_PrintPreallocated(cjson, output, length, format);
    }
}
void *aws_json_node_from_string(char* string) {
    if (string == NULL) {
        return NULL;
    }
    cJSON *cjson = cJSON_Parse(string);
    return (void*)cjson;
}
bool aws_json_node_is_valid(void *node) {
    cJSON *cjson = (cJSON*)node;
    if (node != NULL) {
        return !cJSON_IsInvalid(cjson);
    }
    return false;
}
