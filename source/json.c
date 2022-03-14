/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/common/byte_buf.h>
#include <aws/common/string.h>

#include <aws/common/json.h>

#include <aws/common/external/cJSON.h>

static struct aws_allocator *s_aws_json_module_allocator = NULL;
static bool s_aws_json_module_initialized = false;

struct aws_json_value *aws_json_new_string(struct aws_allocator *allocator, const struct aws_byte_cursor cursor) {
    struct aws_string *tmp = aws_string_new_from_cursor((struct aws_allocator *)allocator, &cursor);
    void *ret_val = cJSON_CreateString(aws_string_c_str(tmp));
    aws_string_destroy_secure(tmp);
    return ret_val;
}

struct aws_json_value *aws_json_new_number(struct aws_allocator *allocator, double number) {
    (void)(allocator); // prevent warnings over unused parameter
    return (void *)(uintptr_t)cJSON_CreateNumber(number);
}

struct aws_json_value *aws_json_new_array(struct aws_allocator *allocator) {
    (void)(allocator); // prevent warnings over unused parameter
    return (void *)(uintptr_t)cJSON_CreateArray();
}

struct aws_json_value *aws_json_new_boolean(struct aws_allocator *allocator, const bool boolean) {
    (void)(allocator); // prevent warnings over unused parameter
    return (void *)(uintptr_t)cJSON_CreateBool(boolean);
}

struct aws_json_value *aws_json_new_null(struct aws_allocator *allocator) {
    (void)(allocator); // prevent warnings over unused parameter
    return (void *)(uintptr_t)cJSON_CreateNull();
}

struct aws_json_value *aws_json_new_object(struct aws_allocator *allocator) {
    (void)(allocator); // prevent warnings over unused parameter
    return (void *)(uintptr_t)cJSON_CreateObject();
}

int aws_json_value_get_string(const struct aws_json_value *value, struct aws_byte_cursor *output) {
    struct cJSON *cjson = (struct cJSON *)value;
    if (cJSON_IsString(cjson)) {
        *output = aws_byte_cursor_from_c_str(cJSON_GetStringValue(cjson));
        return AWS_OP_SUCCESS;
    }
    return AWS_OP_ERR;
}

int aws_json_value_get_number(const struct aws_json_value *value, double *output) {
    struct cJSON *cjson = (struct cJSON *)value;
    if (cJSON_IsNumber(cjson)) {
        *output = cjson->valuedouble;
        return AWS_OP_SUCCESS;
    }
    return AWS_OP_ERR;
}

int aws_json_value_get_boolean(const struct aws_json_value *value, bool *output) {
    struct cJSON *cjson = (struct cJSON *)value;
    if (cJSON_IsBool(cjson)) {
        *output = cjson->type == cJSON_True;
        return AWS_OP_SUCCESS;
    }
    return AWS_OP_ERR;
}

int aws_json_value_add_to_object(
    struct aws_json_value *object,
    const struct aws_byte_cursor cursor,
    struct aws_json_value *value) {
    struct cJSON *cjson = (struct cJSON *)object;
    if (cJSON_IsObject(cjson)) {
        struct cJSON *cjson_value = (struct cJSON *)value;
        int return_result = AWS_OP_ERR;
        struct aws_string *tmp = aws_string_new_from_cursor(s_aws_json_module_allocator, &cursor);
        if (cJSON_HasObjectItem(cjson, aws_string_c_str(tmp)) == false) {
            cJSON_AddItemToObject(cjson, aws_string_c_str(tmp), cjson_value);
            return_result = AWS_OP_SUCCESS;
        }
        aws_string_destroy_secure(tmp);
        return return_result;
    }
    return aws_raise_error(AWS_ERROR_INVALID_ARGUMENT);
}

struct aws_json_value *aws_json_value_get_from_object(
    const struct aws_json_value *object,
    const struct aws_byte_cursor cursor) {
    struct cJSON *cjson = (struct cJSON *)object;
    void *return_value = NULL;
    if (cJSON_IsObject(cjson)) {
        struct aws_string *tmp = aws_string_new_from_cursor(s_aws_json_module_allocator, &cursor);
        return_value = (void *)cJSON_GetObjectItem(cjson, aws_string_c_str(tmp));
        aws_string_destroy_secure(tmp);
    }
    return return_value;
}

bool aws_json_value_check_has_in_object(const struct aws_json_value *object, const struct aws_byte_cursor cursor) {
    struct cJSON *cjson = (struct cJSON *)object;
    if (cJSON_IsObject(cjson)) {
        bool return_value = false;
        struct aws_string *tmp = aws_string_new_from_cursor(s_aws_json_module_allocator, &cursor);
        if (cJSON_HasObjectItem(cjson, aws_string_c_str(tmp))) {
            return_value = true;
        }
        aws_string_destroy_secure(tmp);
        return return_value;
    }
    return false;
}

int aws_json_value_remove_from_object(struct aws_json_value *object, const struct aws_byte_cursor cursor) {
    struct cJSON *cjson = (struct cJSON *)object;
    if (cJSON_IsObject(cjson)) {
        int return_value = AWS_ERROR_INVALID_INDEX;
        struct aws_string *tmp = aws_string_new_from_cursor(s_aws_json_module_allocator, &cursor);
        if (cJSON_HasObjectItem(cjson, aws_string_c_str(tmp))) {
            cJSON_DeleteItemFromObject(cjson, aws_string_c_str(tmp));
            return_value = AWS_OP_SUCCESS;
        }
        aws_string_destroy_secure(tmp);
        return return_value;
    }
    return aws_raise_error(AWS_ERROR_INVALID_ARGUMENT);
}

int aws_json_value_add_to_array(struct aws_json_value *array, const struct aws_json_value *value) {
    struct cJSON *cjson = (struct cJSON *)array;
    if (cJSON_IsArray(cjson)) {
        struct cJSON *cjson_value = (struct cJSON *)value;
        cJSON_AddItemToArray(cjson, cjson_value);
        return AWS_OP_SUCCESS;
    }
    return aws_raise_error(AWS_ERROR_INVALID_ARGUMENT);
}

struct aws_json_value *aws_json_value_get_from_array(const struct aws_json_value *array, const size_t index) {
    struct cJSON *cjson = (struct cJSON *)array;
    if (cJSON_IsArray(cjson)) {
        if (index > (size_t)cJSON_GetArraySize(cjson)) {
            aws_raise_error(AWS_ERROR_INVALID_INDEX);
            return NULL;
        }
        return (void *)(uintptr_t)cJSON_GetArrayItem(cjson, (int)index);
    }
    return NULL;
}

size_t aws_json_value_count_in_array(const struct aws_json_value *array) {
    struct cJSON *cjson = (struct cJSON *)array;
    if (cJSON_IsArray(cjson)) {
        return cJSON_GetArraySize(cjson);
    }
    return 0;
}

int aws_json_value_remove_from_array(struct aws_json_value *array, const size_t index) {
    struct cJSON *cjson = (struct cJSON *)array;
    if (cJSON_IsArray(cjson)) {
        if (index > 0 && index < (size_t)cJSON_GetArraySize(cjson)) {
            cJSON_DeleteItemFromArray(cjson, (int)index);
            return AWS_OP_SUCCESS;
        }
        return aws_raise_error(AWS_ERROR_INVALID_INDEX);
    }
    return aws_raise_error(AWS_ERROR_INVALID_ARGUMENT);
}

bool aws_json_value_is_string(const struct aws_json_value *value) {
    struct cJSON *cjson = (struct cJSON *)value;
    if (cjson == NULL) {
        return aws_raise_error(AWS_ERROR_INVALID_ARGUMENT);
    }
    if (cJSON_IsString(cjson) == true) {
        return true;
    }
    return false;
}

bool aws_json_value_is_number(const struct aws_json_value *value) {
    struct cJSON *cjson = (struct cJSON *)value;
    if (cjson == NULL) {
        return aws_raise_error(AWS_ERROR_INVALID_ARGUMENT);
    }
    if (cJSON_IsNumber(cjson) == true) {
        return true;
    }
    return false;
}

bool aws_json_value_is_array(const struct aws_json_value *value) {
    struct cJSON *cjson = (struct cJSON *)value;
    if (cjson == NULL) {
        return aws_raise_error(AWS_ERROR_INVALID_ARGUMENT);
    }
    if (cJSON_IsArray(cjson) == true) {
        return true;
    }
    return false;
}

bool aws_json_value_is_boolean(const struct aws_json_value *value) {
    struct cJSON *cjson = (struct cJSON *)value;
    if (cjson == NULL) {
        return aws_raise_error(AWS_ERROR_INVALID_ARGUMENT);
    }
    if (cJSON_IsBool(cjson) == true) {
        return true;
    }
    return false;
}

bool aws_json_value_is_null(const struct aws_json_value *value) {
    struct cJSON *cjson = (struct cJSON *)value;
    if (cjson == NULL) {
        return aws_raise_error(AWS_ERROR_INVALID_ARGUMENT);
    }
    if (cJSON_IsNull(cjson) == true) {
        return true;
    }
    return false;
}

bool aws_json_value_is_object(const struct aws_json_value *value) {
    struct cJSON *cjson = (struct cJSON *)value;
    if (cjson == NULL) {
        return aws_raise_error(AWS_ERROR_INVALID_ARGUMENT);
    }
    if (cJSON_IsObject(cjson) == true) {
        return true;
    }
    return false;
}

void *aws_cJSON_alloc(size_t sz) {
    return aws_mem_acquire(s_aws_json_module_allocator, sz);
}

void aws_cJSON_free(void *ptr) {
    aws_mem_release(s_aws_json_module_allocator, ptr);
}

void aws_json_module_init(struct aws_allocator *allocator) {
    if (!s_aws_json_module_initialized) {
        s_aws_json_module_allocator = (struct aws_allocator *)allocator;
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

int aws_json_value_destroy(struct aws_json_value *value) {
    struct cJSON *cjson = (struct cJSON *)value;
    if (cjson != NULL) {
        cJSON_Delete(cjson);
        return AWS_OP_SUCCESS;
    }
    return aws_raise_error(AWS_ERROR_INVALID_ARGUMENT);
}

int aws_json_value_to_string(const struct aws_json_value *value, struct aws_byte_buf *output) {
    struct cJSON *cjson = (struct cJSON *)value;
    if (value != NULL) {
        char *tmp = cJSON_PrintUnformatted(cjson);
        *output = aws_byte_buf_from_c_str(tmp);
        output->allocator = s_aws_json_module_allocator;
        return AWS_OP_SUCCESS;
    }
    return aws_raise_error(AWS_ERROR_INVALID_ARGUMENT);
}

int aws_json_value_to_string_formatted(const struct aws_json_value *value, struct aws_byte_buf *output) {
    struct cJSON *cjson = (struct cJSON *)value;
    if (value != NULL) {
        char *tmp = cJSON_Print(cjson);
        *output = aws_byte_buf_from_c_str(tmp);
        output->allocator = s_aws_json_module_allocator;
        return AWS_OP_SUCCESS;
    }
    return aws_raise_error(AWS_ERROR_INVALID_ARGUMENT);
}

struct aws_json_value *aws_json_value_new_from_string(
    struct aws_allocator *allocator,
    const struct aws_byte_cursor cursor) {
    struct aws_string *tmp = aws_string_new_from_cursor((struct aws_allocator *)allocator, &cursor);
    struct cJSON *cjson = cJSON_Parse(aws_string_c_str(tmp));
    aws_string_destroy_secure(tmp);
    return (void *)cjson;
}
