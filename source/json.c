/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include "aws/common/json.h"

#include "aws/common/external/cJSON.h"

struct aws_json_node *aws_json_string_new(char *string) {
    return (void *)(uintptr_t)cJSON_CreateString(string);
}

struct aws_json_node *aws_json_number_new(double number) {
    return (void *)(uintptr_t)cJSON_CreateNumber(number);
}

struct aws_json_node *aws_json_array_new(void) {
    return (void *)(uintptr_t)cJSON_CreateArray();
}

struct aws_json_node *aws_json_boolean_new(bool boolean) {
    return (void *)(uintptr_t)cJSON_CreateBool(boolean);
}

struct aws_json_node *aws_json_null_new(void) {
    return (void *)(uintptr_t)cJSON_CreateNull();
}

struct aws_json_node *aws_json_object_new(void) {
    return (void *)(uintptr_t)cJSON_CreateObject();
}

int aws_json_string_get(struct aws_json_node *node, char *output) {
    struct cJSON *cjson = (struct cJSON *)node;
    if (cJSON_IsString(cjson)) {
        output = cJSON_GetStringValue(cjson);
        return AWS_OP_SUCCESS;
    }
    return AWS_OP_ERR;
}

int aws_json_number_get(struct aws_json_node *node, double *output) {
    struct cJSON *cjson = (struct cJSON *)node;
    if (cJSON_IsNumber(cjson)) {
        output = &cjson->valuedouble;
        return AWS_OP_SUCCESS;
    }
    return AWS_OP_ERR;
}

int aws_json_boolean_get(struct aws_json_node *node, bool *output) {
    struct cJSON *cjson = (struct cJSON *)node;
    if (cJSON_IsBool(cjson)) {
        if (cjson->type == cJSON_True) {
            *output = true;
        } else {
            *output = false;
        }
        return AWS_OP_SUCCESS;
    }
    return AWS_OP_ERR;
}

int aws_json_object_add(struct aws_json_node *object, char *key, struct aws_json_node *node) {
    struct cJSON *cjson = (struct cJSON *)object;
    if (cJSON_IsObject(cjson)) {
        struct cJSON *cjson_node = (struct cJSON *)node;
        if (cJSON_HasObjectItem(cjson, key) == false) {
            cJSON_AddItemToObject(cjson, key, cjson_node);
            return AWS_OP_SUCCESS;
        }
        return AWS_OP_ERR;
    }
    return aws_raise_error(AWS_ERROR_INVALID_ARGUMENT);
}

struct aws_json_node *aws_json_object_get(struct aws_json_node *object, char *key) {
    struct cJSON *cjson = (struct cJSON *)object;
    if (cJSON_IsObject(cjson)) {
        return (void *)cJSON_GetObjectItem(cjson, key);
    }
    return NULL;
}

struct aws_json_node *aws_json_object_get_insensitive(struct aws_json_node *object, char *key) {
    struct cJSON *cjson = (struct cJSON *)object;
    if (cJSON_IsObject(cjson)) {
        return (void *)cJSON_GetObjectItemCaseSensitive(cjson, key);
    }
    return NULL;
}

int aws_json_object_has(struct aws_json_node *object, char *key) {
    struct cJSON *cjson = (struct cJSON *)object;
    if (cJSON_IsObject(cjson)) {
        if (cJSON_HasObjectItem(cjson, key)) {
            return AWS_OP_SUCCESS;
        }
        return AWS_OP_ERR;
    }
    return aws_raise_error(AWS_ERROR_INVALID_ARGUMENT);
}

int aws_json_object_remove(struct aws_json_node *object, char *key) {
    struct cJSON *cjson = (struct cJSON *)object;
    if (cJSON_IsObject(cjson)) {
        if (cJSON_HasObjectItem(cjson, key)) {
            cJSON_DeleteItemFromObject(cjson, key);
            return AWS_OP_SUCCESS;
        }
        return AWS_OP_ERR;
    }
    return aws_raise_error(AWS_ERROR_INVALID_ARGUMENT);
}

int aws_json_array_add(struct aws_json_node *array, struct aws_json_node *node) {
    struct cJSON *cjson = (struct cJSON *)array;
    if (cJSON_IsArray(cjson)) {
        struct cJSON *cjson_node = (struct cJSON *)node;
        cJSON_AddItemToArray(cjson, cjson_node);
        return AWS_OP_SUCCESS;
    }
    return aws_raise_error(AWS_ERROR_INVALID_ARGUMENT);
}

struct aws_json_node *aws_json_array_get(struct aws_json_node *array, size_t index) {
    struct cJSON *cjson = (struct cJSON *)array;
    if (cJSON_IsArray(cjson)) {
        if (index < 0 || index > cJSON_GetArraySize(cjson)) {
            aws_raise_error(AWS_ERROR_INVALID_INDEX);
            return NULL;
        }
        return (void *)(uintptr_t)cJSON_GetArrayItem(cjson, (int)index);
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

int aws_json_array_remove(struct aws_json_node *array, size_t index) {
    struct cJSON *cjson = (struct cJSON *)array;
    if (cJSON_IsArray(cjson)) {
        if (index > 0 && index < cJSON_GetArraySize(cjson)) {
            cJSON_DeleteItemFromArray(cjson, index);
            return AWS_OP_SUCCESS;
        }
        return aws_raise_error(AWS_ERROR_INVALID_INDEX);
    }
    return aws_raise_error(AWS_ERROR_INVALID_ARGUMENT);
}

bool aws_json_is_string(struct aws_json_node *node) {
    struct cJSON *cjson = (struct cJSON *)node;
    if (cjson == NULL) {
        return aws_raise_error(AWS_ERROR_INVALID_ARGUMENT);
    }
    if (cJSON_IsString(cjson) == true) {
        return true;
    }
    return false;
}

bool aws_json_is_number(struct aws_json_node *node) {
    struct cJSON *cjson = (struct cJSON *)node;
    if (cjson == NULL) {
        return aws_raise_error(AWS_ERROR_INVALID_ARGUMENT);
    }
    if (cJSON_IsNumber(cjson) == true) {
        return true;
    }
    return false;
}

bool aws_json_is_array(struct aws_json_node *node) {
    struct cJSON *cjson = (struct cJSON *)node;
    if (cjson == NULL) {
        return aws_raise_error(AWS_ERROR_INVALID_ARGUMENT);
    }
    if (cJSON_IsArray(cjson) == true) {
        return true;
    }
    return false;
}

bool aws_json_is_boolean(struct aws_json_node *node) {
    struct cJSON *cjson = (struct cJSON *)node;
    if (cjson == NULL) {
        return aws_raise_error(AWS_ERROR_INVALID_ARGUMENT);
    }
    if (cJSON_IsBool(cjson) == true) {
        return true;
    }
    return false;
}

bool aws_json_is_null(struct aws_json_node *node) {
    struct cJSON *cjson = (struct cJSON *)node;
    if (cjson == NULL) {
        return aws_raise_error(AWS_ERROR_INVALID_ARGUMENT);
    }
    if (cJSON_IsNull(cjson) == true) {
        return true;
    }
    return false;
}

bool aws_json_is_object(struct aws_json_node *node) {
    struct cJSON *cjson = (struct cJSON *)node;
    if (cjson == NULL) {
        return aws_raise_error(AWS_ERROR_INVALID_ARGUMENT);
    }
    if (cJSON_IsObject(cjson) == true) {
        return true;
    }
    return false;
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

int aws_json_destroy(struct aws_json_node *node) {
    struct cJSON *cjson = (struct cJSON *)node;
    if (cjson != NULL) {
        cJSON_Delete(cjson);
        return AWS_OP_SUCCESS;
    }
    return aws_raise_error(AWS_ERROR_INVALID_ARGUMENT);
}

int aws_json_free(struct aws_json_node *node) {
    struct cJSON *cjson = (struct cJSON *)node;
    if (cjson != NULL) {
        cJSON_free(cjson);
        return AWS_OP_SUCCESS;
    }
    return aws_raise_error(AWS_ERROR_INVALID_ARGUMENT);
}

char *aws_json_to_string(struct aws_json_node *node) {
    struct cJSON *cjson = (struct cJSON *)node;
    if (node != NULL) {
        return cJSON_PrintUnformatted(cjson);
    }
    return NULL;
}

char *aws_json_to_string_formatted(struct aws_json_node *node) {
    struct cJSON *cjson = (struct cJSON *)node;
    if (node != NULL) {
        return cJSON_Print(cjson);
    }
    return NULL;
}

struct aws_json_node *aws_json_from_string(char *string) {
    if (string == NULL) {
        return NULL;
    }
    struct cJSON *cjson = cJSON_Parse(string);
    return (void *)cjson;
}

int aws_json_is_valid(struct aws_json_node *node) {
    struct cJSON *cjson = (struct cJSON *)node;
    if (node != NULL) {
        if (!cJSON_IsInvalid(cjson)) {
            return AWS_OP_SUCCESS;
        }
    }
    return AWS_OP_ERR;
}
