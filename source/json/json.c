/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/common/json/json.h>

#include <aws/common/byte_buf.h>
#include <aws/common/date_time.h>
#include <aws/common/logging.h>

struct aws_allocator *aws_json_module_allocator = NULL;
bool aws_json_module_initialized = false;

void *aws_cJSON_alloc(size_t sz) {
    return aws_mem_acquire(aws_json_module_allocator, sz);
}

void aws_cJSON_free(void *ptr) {
    aws_mem_release(aws_json_module_allocator, ptr);
}

void aws_json_init(struct aws_allocator *allocator) {
    if (!aws_json_module_initialized) {
        aws_json_module_allocator = allocator;
        struct cJSON_Hooks allocation_hooks = {.malloc_fn = aws_cJSON_alloc, .free_fn = aws_cJSON_free};
        cJSON_InitHooks(&allocation_hooks);
        aws_json_module_initialized = true;
    }
}

void aws_json_clean_up() {
    if (aws_json_module_initialized) {
        aws_json_module_allocator = NULL;
        aws_json_module_initialized = false;
    }
}

struct aws_json_parse_credentials_results aws_json_parse_credentials_from_cjson(
    struct cJSON *document_root,
    const struct aws_json_parse_credentials_options *options) {

    AWS_FATAL_ASSERT(document_root);
    AWS_FATAL_ASSERT(options);
    AWS_FATAL_ASSERT(options->access_key_id_name);
    AWS_FATAL_ASSERT(options->secrete_access_key_name);

    if (options->token_required) {
        AWS_FATAL_ASSERT(options->token_name);
    }
    if (options->expiration_required) {
        AWS_FATAL_ASSERT(options->expiration_name);
    }

    struct aws_json_parse_credentials_results return_val;
    return_val.access_key_id = NULL;
    return_val.secret_access_key = NULL;
    return_val.token = NULL;
    return_val.creds_expiration = NULL;

    cJSON *access_key_id = NULL;
    cJSON *secrete_access_key = NULL;
    cJSON *token = NULL;
    cJSON *creds_expiration = NULL;

    bool parse_error = true;

    //
    // Pull out the credentials components
    //

    access_key_id = aws_json_get_cjson_with_validate(document_root, options->access_key_id_name, "AccessKeyId");
    if (access_key_id == NULL) {
        goto done;
    }
    return_val.access_key_id = access_key_id->valuestring;

    secrete_access_key =
        aws_json_get_cjson_with_validate(document_root, options->secrete_access_key_name, "SecretAccessKey");
    if (secrete_access_key == NULL) {
        goto done;
    }
    return_val.secret_access_key = secrete_access_key->valuestring;

    if (options->token_name) {
        token = aws_json_get_cjson_with_validate(document_root, options->token_name, "Token");
        if (token == NULL) {
            goto done;
        }
        return_val.token = token->valuestring;
    }

    if (options->expiration_name) {
        creds_expiration = aws_json_get_cjson_with_validate(document_root, options->expiration_name, "Expiration");
        if (creds_expiration == NULL) {
            goto done;
        }
        return_val.creds_expiration = creds_expiration->valuestring;
    }

    uint64_t expiration_timepoint_in_seconds = UINT64_MAX;
    if (creds_expiration) {
        struct aws_byte_cursor creds_expiration_cursor = aws_byte_cursor_from_c_str(creds_expiration->valuestring);
        if (options->expiration_required && creds_expiration_cursor.len == 0) {
            AWS_LOGF_ERROR(
                AWS_LS_COMMON_GENERAL, "Parsed an unexpected credentials json document with empty expiration.");
            goto done;
        }
        if (creds_expiration_cursor.len != 0) {
            struct aws_date_time expiration;
            if (aws_date_time_init_from_str_cursor(&expiration, &creds_expiration_cursor, AWS_DATE_FORMAT_ISO_8601) ==
                AWS_OP_ERR) {
                AWS_LOGF_ERROR(
                    AWS_LS_COMMON_GENERAL, "Expiration in Json document is not a valid ISO_8601 date string.");
                if (options->expiration_required) {
                    goto done;
                }
            } else {
                expiration_timepoint_in_seconds = (uint64_t)aws_date_time_as_epoch_secs(&expiration);
            }
        }
    }
    return_val.expiration_timepoint_in_seconds = expiration_timepoint_in_seconds;
    parse_error = false;

done:

    if (parse_error) {
        aws_raise_error(AWS_OP_ERR);
    }

    return return_val;
}

struct cJSON *aws_json_create_cjson() {
    return cJSON_CreateObject();
}

bool aws_json_create_and_add_cjson(cJSON *object, const char *item_key, cJSON *output) {
    output = aws_json_create_cjson();
    if (output == NULL) {
        return false;
    }
    aws_json_add_item_to_cjson(object, item_key, output);
    return true;
}

struct cJSON *aws_json_create_cjson_array() {
    return cJSON_CreateArray();
}

bool aws_json_create_and_add_cjson_array(cJSON *object, const char *item_key, cJSON *output) {
    output = aws_json_create_cjson_array();
    if (output == NULL) {
        return false;
    }
    aws_json_add_item_to_cjson(object, item_key, output);
    return true;
}

cJSON *aws_json_create_cjson_number(const double item_value) {
    return cJSON_CreateNumber(item_value);
}
cJSON *aws_json_create_cjson_string(const char *item_value) {
    return cJSON_CreateString(item_value);
}

cJSON *aws_json_parse_cjson_from_string(const char *string) {
    cJSON *object = cJSON_Parse(string);
    if (object == NULL) {
        AWS_LOGF_ERROR(AWS_LS_COMMON_GENERAL, "Failed to parse document as Json document.");
        return NULL;
    }
    return object;
}

void aws_json_add_item_to_cjson(cJSON *object, const char *item_key, cJSON *item_value) {
    cJSON_AddItemToObject(object, item_key, item_value);
}

void aws_json_add_item_to_cjson_array(cJSON *array, cJSON *item_value) {
    cJSON_AddItemToArray(array, item_value);
}

bool aws_json_add_string_to_cjson(cJSON *object, const char *item_key, const char *item_value) {
    if (cJSON_AddStringToObject(object, item_key, item_value) == NULL) {
        return false;
    }
    return true;
}

bool aws_json_add_number_to_cjson(cJSON *object, const char *item_key, const double item_value) {
    if (cJSON_AddNumberToObject(object, item_key, item_value) == NULL) {
        return false;
    }
    return true;
}

cJSON *aws_json_get_cjson(cJSON *object, const char *item_key) {
    return cJSON_GetObjectItem(object, item_key);
}

cJSON *aws_json_get_cjson_with_validate(cJSON *object, const char *item_key, const char *log_key_name) {
    cJSON *return_val = aws_json_get_cjson(object, item_key);
    if (!cJSON_IsString(return_val) || (return_val->valuestring == NULL)) {
        AWS_LOGF_ERROR(AWS_LS_COMMON_GENERAL, "Failed to parse from Json document: %s", log_key_name);
        return NULL;
    }
    return return_val;
}

cJSON *aws_json_get_cjson_case_sensitive(cJSON *object, const char *item_key) {
    return cJSON_GetObjectItemCaseSensitive(object, item_key);
}

char *aws_json_get_cjson_string(cJSON *object) {
    return cJSON_GetStringValue(object);
}

cJSON *aws_json_get_cjson_array_item(cJSON *object, int index) {
    return cJSON_GetArrayItem(object, index);
}

bool aws_json_is_cjson_object(cJSON *object) {
    return cJSON_IsObject(object);
}

bool aws_json_is_cjson_number(cJSON *object) {
    return cJSON_IsNumber(object);
}

bool aws_json_is_cjson_array(cJSON *object) {
    return cJSON_IsArray(object);
}

char *aws_json_print_unformatted_cjson(cJSON *object) {
    return cJSON_PrintUnformatted(object);
}

void aws_json_print_preallocated_cjson(cJSON *object, char *output, int length, int fmt) {
    cJSON_PrintPreallocated(object, output, length, fmt);
}

void aws_json_delete_cjson(cJSON *object) {
    cJSON_Delete(object);
}

void aws_json_free_cjson(cJSON *object) {
    cJSON_free(object);
}
