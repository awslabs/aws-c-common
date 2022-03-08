/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/common/byte_buf.h>
#include <aws/common/string.h>

#include "aws/common/json.h"

#include "aws/common/external/cJSON.h"

struct aws_json_value *aws_json_string_new(const struct aws_byte_cursor *cursor, const struct aws_allocator *allocator) {
    struct aws_string *tmp = aws_string_new_from_cursor((struct aws_allocator *)allocator, cursor);
    void *ret_val = cJSON_CreateString(aws_string_c_str(tmp));
    aws_string_destroy_secure(tmp);
    return ret_val;
}

struct aws_json_value *aws_json_number_new(const double number, const struct aws_allocator *allocator) {
    return (void *)(uintptr_t)cJSON_CreateNumber(number);
}

struct aws_json_value *aws_json_array_new(const struct aws_allocator *allocator) {
    return (void *)(uintptr_t)cJSON_CreateArray();
}

struct aws_json_value *aws_json_boolean_new(const bool boolean, const struct aws_allocator *allocator) {
    return (void *)(uintptr_t)cJSON_CreateBool(boolean);
}

struct aws_json_value *aws_json_null_new(const struct aws_allocator *allocator) {
    return (void *)(uintptr_t)cJSON_CreateNull();
}

struct aws_json_value *aws_json_object_new(const struct aws_allocator *allocator) {
    return (void *)(uintptr_t)cJSON_CreateObject();
}

int aws_json_value_get_string(const struct aws_json_value *node, struct aws_byte_cursor *output) {
    struct cJSON *cjson = (struct cJSON *)node;
    if (cJSON_IsString(cjson)) {
        *output = aws_byte_cursor_from_c_str(cJSON_GetStringValue(cjson));
        return AWS_OP_SUCCESS;
    }
    return AWS_OP_ERR;
}

int aws_json_value_get_number(const struct aws_json_value *node, double *output) {
    struct cJSON *cjson = (struct cJSON *)node;
    if (cJSON_IsNumber(cjson)) {
        memcpy(output, &cjson->valuedouble, sizeof(double *));
        return AWS_OP_SUCCESS;
    }
    return AWS_OP_ERR;
}

int aws_json_value_get_boolean(const struct aws_json_value *node, bool *output) {
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

int aws_json_object_add(const struct aws_json_value *object, const struct aws_byte_cursor *cursor,
                        const struct aws_allocator *allocator, const struct aws_json_value *node) {
    struct cJSON *cjson = (struct cJSON *)object;
    if (cJSON_IsObject(cjson)) {
        struct cJSON *cjson_node = (struct cJSON *)node;
        int return_result = AWS_OP_ERR;
        struct aws_string* tmp = aws_string_new_from_cursor((struct aws_allocator *) allocator, cursor);
        if (cJSON_HasObjectItem(cjson, aws_string_c_str(tmp)) == false) {
            cJSON_AddItemToObject(cjson, aws_string_c_str(tmp), cjson_node);
            return_result = AWS_OP_SUCCESS;
        }
        aws_string_destroy_secure(tmp);
        return return_result;
    }
    return aws_raise_error(AWS_ERROR_INVALID_ARGUMENT);
}

struct aws_json_value *aws_json_object_get(const struct aws_json_value *object, const struct aws_byte_cursor *cursor,
                                           const struct aws_allocator *allocator) {
    struct cJSON *cjson = (struct cJSON *)object;
    void *return_value = NULL;
    if (cJSON_IsObject(cjson)) {
        struct aws_string* tmp = aws_string_new_from_cursor((struct aws_allocator *) allocator, cursor);
        return_value = (void *)cJSON_GetObjectItem(cjson, aws_string_c_str(tmp));
        aws_string_destroy_secure(tmp);
    }
    return return_value;
}

struct aws_json_value *aws_json_object_get_insensitive(const struct aws_json_value *object,
                                                       const struct aws_byte_cursor *cursor,
                                                       const struct aws_allocator *allocator) {
    struct cJSON *cjson = (struct cJSON *)object;
    void *return_value = NULL;
    if (cJSON_IsObject(cjson)) {
        struct aws_string* tmp = aws_string_new_from_cursor((struct aws_allocator *) allocator, cursor);
        return_value = (void *)cJSON_GetObjectItemCaseSensitive(cjson, aws_string_c_str(tmp));
        aws_string_destroy_secure(tmp);
    }
    return return_value;
}

int aws_json_object_has(const struct aws_json_value *object, const struct aws_byte_cursor *cursor,
                        const struct aws_allocator *allocator) {
    struct cJSON *cjson = (struct cJSON *)object;
    if (cJSON_IsObject(cjson)) {
        int return_value = AWS_OP_ERR;
        struct aws_string* tmp = aws_string_new_from_cursor((struct aws_allocator *) allocator, cursor);
        if (cJSON_HasObjectItem(cjson, aws_string_c_str(tmp))) {
            return_value = AWS_OP_SUCCESS;
        }
        aws_string_destroy_secure(tmp);
        return return_value;
    }
    return aws_raise_error(AWS_ERROR_INVALID_ARGUMENT);
}

int aws_json_object_remove(const struct aws_json_value *object, const struct aws_byte_cursor *cursor,
                           const struct aws_allocator *allocator) {
    struct cJSON *cjson = (struct cJSON *)object;
    if (cJSON_IsObject(cjson)) {
        int return_value = AWS_OP_ERR;
        struct aws_string* tmp = aws_string_new_from_cursor((struct aws_allocator *) allocator, cursor);
        if (cJSON_HasObjectItem(cjson, aws_string_c_str(tmp))) {
            cJSON_DeleteItemFromObject(cjson, aws_string_c_str(tmp));
            return_value = AWS_OP_SUCCESS;
        }
        aws_string_destroy_secure(tmp);
        return return_value;
    }
    return aws_raise_error(AWS_ERROR_INVALID_ARGUMENT);
}

int aws_json_array_add(const struct aws_json_value *array, const struct aws_json_value *node) {
    struct cJSON *cjson = (struct cJSON *)array;
    if (cJSON_IsArray(cjson)) {
        struct cJSON *cjson_node = (struct cJSON *)node;
        cJSON_AddItemToArray(cjson, cjson_node);
        return AWS_OP_SUCCESS;
    }
    return aws_raise_error(AWS_ERROR_INVALID_ARGUMENT);
}

struct aws_json_value *aws_json_array_get(const struct aws_json_value *array, const size_t index) {
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

int aws_json_array_get_count(const struct aws_json_value *array) {
    struct cJSON *cjson = (struct cJSON *)array;
    if (cJSON_IsArray(cjson)) {
        return cJSON_GetArraySize(cjson);
    }
    return 0;
}

int aws_json_array_remove(const struct aws_json_value *array, const size_t index) {
    struct cJSON *cjson = (struct cJSON *)array;
    if (cJSON_IsArray(cjson)) {
        if (index > 0 && index < cJSON_GetArraySize(cjson)) {
            cJSON_DeleteItemFromArray(cjson, (int)index);
            return AWS_OP_SUCCESS;
        }
        return aws_raise_error(AWS_ERROR_INVALID_INDEX);
    }
    return aws_raise_error(AWS_ERROR_INVALID_ARGUMENT);
}

bool aws_json_is_string(const struct aws_json_value *node) {
    struct cJSON *cjson = (struct cJSON *)node;
    if (cjson == NULL) {
        return aws_raise_error(AWS_ERROR_INVALID_ARGUMENT);
    }
    if (cJSON_IsString(cjson) == true) {
        return true;
    }
    return false;
}

bool aws_json_is_number(const struct aws_json_value *node) {
    struct cJSON *cjson = (struct cJSON *)node;
    if (cjson == NULL) {
        return aws_raise_error(AWS_ERROR_INVALID_ARGUMENT);
    }
    if (cJSON_IsNumber(cjson) == true) {
        return true;
    }
    return false;
}

bool aws_json_is_array(const struct aws_json_value *node) {
    struct cJSON *cjson = (struct cJSON *)node;
    if (cjson == NULL) {
        return aws_raise_error(AWS_ERROR_INVALID_ARGUMENT);
    }
    if (cJSON_IsArray(cjson) == true) {
        return true;
    }
    return false;
}

bool aws_json_is_boolean(const struct aws_json_value *node) {
    struct cJSON *cjson = (struct cJSON *)node;
    if (cjson == NULL) {
        return aws_raise_error(AWS_ERROR_INVALID_ARGUMENT);
    }
    if (cJSON_IsBool(cjson) == true) {
        return true;
    }
    return false;
}

bool aws_json_is_null(const struct aws_json_value *node) {
    struct cJSON *cjson = (struct cJSON *)node;
    if (cjson == NULL) {
        return aws_raise_error(AWS_ERROR_INVALID_ARGUMENT);
    }
    if (cJSON_IsNull(cjson) == true) {
        return true;
    }
    return false;
}

bool aws_json_is_object(const struct aws_json_value *node) {
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

void aws_json_module_init(const struct aws_allocator *allocator) {
    if (!s_aws_json_module_initialized) {
        s_aws_json_module_allocator = (struct aws_allocator *) allocator;
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

int aws_json_destroy(const struct aws_json_value *node) {
    struct cJSON *cjson = (struct cJSON *)node;
    if (cjson != NULL) {
        cJSON_Delete(cjson);
        return AWS_OP_SUCCESS;
    }
    return aws_raise_error(AWS_ERROR_INVALID_ARGUMENT);
}

int aws_json_to_string(const struct aws_json_value *node, struct aws_byte_cursor *output) {
    struct cJSON *cjson = (struct cJSON *)node;
    if (node != NULL) {
        char *test = cJSON_PrintUnformatted(cjson);
        *output = aws_byte_cursor_from_c_str(test);
        cJSON_free(test);
        return AWS_OP_SUCCESS;
    }
    return AWS_OP_ERR;
}

int aws_json_to_string_formatted(const struct aws_json_value *node, struct aws_byte_buf *output) {
    struct cJSON *cjson = (struct cJSON *)node;
    if (node != NULL) {
        *output = aws_byte_buf_from_c_str(cJSON_Print(cjson));
        return AWS_OP_SUCCESS;
    }
    return AWS_OP_ERR;
}

struct aws_json_value *aws_json_from_string(const struct aws_byte_cursor *cursor, const struct aws_allocator *allocator) {
    if (cursor == NULL) {
        return NULL;
    }
    struct aws_string *tmp = aws_string_new_from_cursor((struct aws_allocator *) allocator, cursor);
    struct cJSON *cjson = cJSON_Parse(aws_string_c_str(tmp));
    aws_string_destroy_secure(tmp);
    return (void *)cjson;
}

int aws_json_is_valid(const struct aws_json_value *node) {
    struct cJSON *cjson = (struct cJSON *)node;
    if (node != NULL) {
        if (!cJSON_IsInvalid(cjson)) {
            return AWS_OP_SUCCESS;
        }
    }
    return AWS_OP_ERR;
}
