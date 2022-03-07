/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/common/json/external/cJSON.h>
#include <aws/common/json/json.h>

struct aws_json_node *aws_json_make_node(void) {
    return (void *)(uintptr_t)cJSON_CreateObject();
}
struct aws_json_node *aws_json_make_node_string(char *string) {
    return (void *)(uintptr_t)cJSON_CreateString(string);
}
struct aws_json_node *aws_json_make_node_number(double number) {
    return (void *)(uintptr_t)cJSON_CreateNumber(number);
}
struct aws_json_node *aws_json_make_node_array(void) {
    return (void *)(uintptr_t)cJSON_CreateArray();
}
struct aws_json_node *aws_json_make_node_boolean(bool boolean) {
    return (void *)(uintptr_t)cJSON_CreateBool(boolean);
}
struct aws_json_node *aws_json_make_node_null(void) {
    return (void *)(uintptr_t)cJSON_CreateNull();
}
struct aws_json_node *aws_json_make_node_object(void) {
    return aws_json_make_node();
}

bool aws_json_set_string(struct aws_json_node *node, char *string) {
    struct cJSON *cjson = (struct cJSON *)node;
    if (cJSON_IsString(cjson)) {
        cjson->valuestring = string;
        return true;
    }
    return false;
}
bool aws_json_set_number(struct aws_json_node *node, double number) {
    struct cJSON *cjson = (struct cJSON *)node;
    if (cJSON_IsNumber(cjson)) {
        cJSON_SetNumberHelper(cjson, number);
        return true;
    }
    return false;
}
bool aws_json_set_boolean(struct aws_json_node *node, bool boolean) {
    struct cJSON *cjson = (struct cJSON *)node;
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

char *aws_json_node_get_string(struct aws_json_node *node) {
    struct cJSON *cjson = (struct cJSON *)node;
    if (cJSON_IsString(cjson)) {
        return cJSON_GetStringValue(cjson);
    }
    return NULL;
}
double *aws_json_node_get_number(struct aws_json_node *node) {
    struct cJSON *cjson = (struct cJSON *)node;
    if (cJSON_IsNumber(cjson)) {
        return &cjson->valuedouble;
    }
    return NULL;
}
bool aws_json_node_get_boolean(struct aws_json_node *node) {
    struct cJSON *cjson = (struct cJSON *)node;
    if (cJSON_IsBool(cjson)) {
        if (cjson->type == cJSON_True) {
            return true;
        } else {
            return false;
        }
    }
    return NULL;
}

bool aws_json_object_add_node(struct aws_json_node *object, char *key, struct aws_json_node *node) {
    struct cJSON *cjson = (struct cJSON *)object;
    if (cJSON_IsObject(cjson)) {
        struct cJSON *cjson_node = (struct cJSON *)node;
        if (cJSON_HasObjectItem(cjson, key) == false) {
            cJSON_AddItemToObject(cjson, key, cjson_node);
            return true;
        }
        return false;
    }
    return false;
}
struct aws_json_node *aws_json_object_get_node(struct aws_json_node *object, char *key) {
    struct cJSON *cjson = (struct cJSON *)object;
    if (cJSON_IsObject(cjson)) {
        return (void *)cJSON_GetObjectItem(cjson, key);
    }
    return NULL;
}
struct aws_json_node *aws_json_object_get_node_case_insensitive(struct aws_json_node *object, char *key) {
    struct cJSON *cjson = (struct cJSON *)object;
    if (cJSON_IsObject(cjson)) {
        return (void *)cJSON_GetObjectItemCaseSensitive(cjson, key);
    }
    return NULL;
}
bool aws_json_object_has_node(struct aws_json_node *object, char *key) {
    struct cJSON *cjson = (struct cJSON *)object;
    if (cJSON_IsObject(cjson)) {
        return cJSON_HasObjectItem(cjson, key);
    }
    return false;
}
bool aws_json_object_delete_node(struct aws_json_node *object, char *key) {
    struct cJSON *cjson = (struct cJSON *)object;
    if (cJSON_IsObject(cjson)) {
        if (cJSON_HasObjectItem(cjson, key)) {
            cJSON_DeleteItemFromObject(cjson, key);
            return true;
        }
    }
    return false;
}
bool aws_json_object_delete_node_with_node(struct aws_json_node *object, struct aws_json_node *node) {
    struct cJSON *cjson = (struct cJSON *)object;
    if (cJSON_IsObject(cjson)) {
        struct cJSON *cjson_node = (struct cJSON *)node;
        if (cjson_node->string != NULL) {
            if (cJSON_HasObjectItem(cjson, cjson_node->string)) {
                cJSON_DeleteItemFromObject(cjson, cjson_node->string);
                return true;
            }
        }
    }
    return false;
}

bool aws_json_array_add_node(struct aws_json_node *array, struct aws_json_node *node) {
    struct cJSON *cjson = (struct cJSON *)array;
    if (cJSON_IsArray(cjson)) {
        struct cJSON *cjson_node = (struct cJSON *)node;
        cJSON_AddItemToArray(cjson, cjson_node);
        return true;
    }
    return false;
}
struct aws_json_node *aws_json_array_get_node(struct aws_json_node *array, int index) {
    struct cJSON *cjson = (struct cJSON *)array;
    if (cJSON_IsArray(cjson)) {
        return (void *)(uintptr_t)cJSON_GetArrayItem(cjson, index);
    }
    return NULL;
}
int aws_json_array_get_count(struct aws_json_node *array) {
    struct cJSON *cjson = (struct cJSON *)array;
    if (cJSON_IsArray(cjson)) {
        return cJSON_GetArraySize(cjson);
    }
    return 0;
}
bool aws_json_array_has_node(struct aws_json_node *array, struct aws_json_node *node) {
    struct cJSON *cjson = (struct cJSON *)array;
    if (cJSON_IsArray(cjson)) {
        struct cJSON *cjson_node = (struct cJSON *)node;

        struct cJSON *array_child = cjson->child;
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
bool aws_json_array_delete_node(struct aws_json_node *array, int index) {
    struct cJSON *cjson = (struct cJSON *)array;
    if (cJSON_IsArray(cjson)) {
        if (index > 0 && index < cJSON_GetArraySize(cjson)) {
            cJSON_DeleteItemFromArray(cjson, index);
            return true;
        }
    }
    return false;
}
bool aws_json_array_delete_node_with_node(struct aws_json_node *array, struct aws_json_node *node) {
    struct cJSON *cjson = (struct cJSON *)array;
    if (cJSON_IsArray(cjson)) {
        struct cJSON *cjson_node = (struct cJSON *)node;
        int index = 0;

        struct cJSON *array_child = cjson->child;
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

bool aws_json_node_is_string(struct aws_json_node *node) {
    struct cJSON *cjson = (struct cJSON *)node;
    return cJSON_IsString(cjson);
}
bool aws_json_node_is_number(struct aws_json_node *node) {
    struct cJSON *cjson = (struct cJSON *)node;
    return cJSON_IsNumber(cjson);
}
bool aws_json_node_is_array(struct aws_json_node *node) {
    struct cJSON *cjson = (struct cJSON *)node;
    return cJSON_IsArray(cjson);
}
bool aws_json_node_is_boolean(struct aws_json_node *node) {
    struct cJSON *cjson = (struct cJSON *)node;
    return cJSON_IsBool(cjson);
}
bool aws_json_node_is_null(struct aws_json_node *node) {
    struct cJSON *cjson = (struct cJSON *)node;
    return cJSON_IsNull(cjson);
}
bool aws_json_node_is_object(struct aws_json_node *node) {
    struct cJSON *cjson = (struct cJSON *)node;
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
bool aws_json_node_delete(struct aws_json_node *node) {
    struct cJSON *cjson = (struct cJSON *)node;
    if (cjson != NULL) {
        cJSON_Delete(cjson);
        return true;
    }
    return false;
}
bool aws_json_node_free(struct aws_json_node *node) {
    struct cJSON *cjson = (struct cJSON *)node;
    if (cjson != NULL) {
        cJSON_free(cjson);
        return true;
    }
    return false;
}

char *aws_json_node_to_string(struct aws_json_node *node) {
    struct cJSON *cjson = (struct cJSON *)node;
    if (node != NULL) {
        return cJSON_PrintUnformatted(cjson);
    }
    return NULL;
}
char *aws_json_node_to_string_formatted(struct aws_json_node *node) {
    struct cJSON *cjson = (struct cJSON *)node;
    if (node != NULL) {
        return cJSON_Print(cjson);
    }
    return NULL;
}
void aws_json_print_to_string_preallocated(struct aws_json_node *node, char *output, int length, bool format) {
    struct cJSON *cjson = (struct cJSON *)node;
    if (node != NULL) {
        cJSON_PrintPreallocated(cjson, output, length, format);
    }
}
struct aws_json_node *aws_json_node_from_string(char *string) {
    if (string == NULL) {
        return NULL;
    }
    struct cJSON *cjson = cJSON_Parse(string);
    return (void *)cjson;
}
bool aws_json_node_is_valid(struct aws_json_node *node) {
    struct cJSON *cjson = (struct cJSON *)node;
    if (node != NULL) {
        return !cJSON_IsInvalid(cjson);
    }
    return false;
}
