/**
* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
* SPDX-License-Identifier: Apache-2.0.
*/

#include <aws/common/json/json.h>

#include <aws/common/byte_buf.h>
#include <aws/common/logging.h>
#include <aws/common/date_time.h>


struct aws_allocator *s_json_module_allocator = NULL;
bool s_json_module_initialized = false;

void *s_cJSON_alloc(size_t sz) {
    return aws_mem_acquire(s_json_module_allocator, sz);
}

void s_cJSON_free(void *ptr) {
    aws_mem_release(s_json_module_allocator, ptr);
}

void s_json_init(struct aws_allocator *allocator) {
    if (!s_json_module_initialized)
    {
        s_json_module_allocator = allocator;
        struct cJSON_Hooks allocation_hooks = {.malloc_fn = s_cJSON_alloc, .free_fn = s_cJSON_free};
        cJSON_InitHooks(&allocation_hooks);
        s_json_module_initialized = true;
    }
}

void s_json_clean_up()
{
    if (s_json_module_initialized)
    {
        s_json_module_allocator = NULL;
        s_json_module_initialized = false;
    }
}

struct aws_json_parse_credentials_from_json_doc_results s_json_parse_credentials_from_cjson_object(
    struct cJSON *document_root,
    const struct aws_json_parse_credentials_from_json_doc_options *options) {

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

    struct aws_json_parse_credentials_from_json_doc_results return_val;
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

    access_key_id = m_get_cjson_if_valid(document_root, options->access_key_id_name, "AccessKeyId");
    if (access_key_id == NULL) {
        goto done;
    }
    return_val.access_key_id = access_key_id->valuestring;

    secrete_access_key = m_get_cjson_if_valid(document_root, options->secrete_access_key_name, "SecretAccessKey");
    if (secrete_access_key == NULL) {
        goto done;
    }
    return_val.secret_access_key = secrete_access_key->valuestring;

    if (options->token_name) {
        token = m_get_cjson_if_valid(document_root, options->token_name, "Token");
        if (token == NULL) {
            goto done;
        }
        return_val.token = token->valuestring;
    }

    if (options->expiration_name) {
        creds_expiration = m_get_cjson_if_valid(document_root, options->expiration_name, "Expiration");
        if (creds_expiration == NULL) {
            goto done;
        }
        return_val.creds_expiration = creds_expiration->valuestring;
    }

    uint64_t expiration_timepoint_in_seconds = UINT64_MAX;
    if (creds_expiration) {
        struct aws_byte_cursor creds_expiration_cursor = aws_byte_cursor_from_c_str(creds_expiration->valuestring);
        if (options->expiration_required && creds_expiration_cursor.len == 0) {
            AWS_LOGF_ERROR(AWS_OP_ERR, "Parsed an unexpected credentials json document with empty expiration.");
            goto done;
        }
        if (creds_expiration_cursor.len != 0) {
            struct aws_date_time expiration;
            if (aws_date_time_init_from_str_cursor(&expiration, &creds_expiration_cursor, AWS_DATE_FORMAT_ISO_8601) == AWS_OP_ERR) {
                AWS_LOGF_ERROR(AWS_OP_ERR, "Expiration in Json document is not a valid ISO_8601 date string.");
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

cJSON *m_get_cjson_if_valid(cJSON *root, const char* name, const char* logName)
{
    cJSON *returnVal = cJSON_GetObjectItem(root, name);
    if (!cJSON_IsString(returnVal) || (returnVal->valuestring == NULL)) {
        AWS_LOGF_ERROR(AWS_OP_ERR, "Failed to parse from Json document: %s", logName);
        return NULL;
    }
    return returnVal;
}



struct cJSON *m_create_cjson()
{
    return cJSON_CreateObject();
}
void m_add_item_to_cjson(cJSON *object, const char* item_key, cJSON *item_value)
{
    cJSON_AddItemToObject(object, item_key, item_value);
}

bool m_create_and_add_cjson(cJSON *object, const char* item_key, cJSON *output)
{
    output = m_create_cjson();
    if (output == NULL)
    {
        return false;
    }
    m_add_item_to_cjson(object, item_key, output);
    return true;
}

bool m_add_string_to_cjson(cJSON *object, const char* item_key, const char* item_value)
{
    if (cJSON_AddStringToObject(object, item_key, item_value) == NULL)
    {
        return false;
    }
    return true;
}
bool m_add_number_to_cjson(cJSON *object, const char* item_key, const double item_value)
{
    if (cJSON_AddNumberToObject(object, item_key, item_value) == NULL)
    {
        return false;
    }
    return true;
}

struct cJSON *m_create_cjson_array()
{
    return cJSON_CreateArray();
}
bool m_create_and_add_cjson_array(cJSON *object, const char* item_key, cJSON *output)
{
    output = m_create_cjson_array();
    if (output == NULL)
    {
        return false;
    }
    m_add_item_to_cjson(object, item_key, output);
    return true;
}

void m_add_item_to_cjson_array(cJSON *array, cJSON* item_value)
{
    cJSON_AddItemToArray(array, item_value);
}

cJSON* m_create_cjson_number(const double item_value)
{
    return cJSON_CreateNumber(item_value);
}
cJSON* m_create_cjson_string(const char* item_value)
{
    return cJSON_CreateString(item_value);
}

char* m_print_unformatted_cjson(cJSON *object)
{
    return cJSON_PrintUnformatted(object);
}

void m_delete_cjson(cJSON *object)
{
    cJSON_Delete(object);
}
void m_free_cjson(cJSON *object)
{
    cJSON_free(object);
}

cJSON* m_parse_cjson(const char* path)
{
    cJSON *object = cJSON_Parse(path);
    if (object == NULL) {
        AWS_LOGF_ERROR(AWS_OP_ERR, "Failed to parse document as Json document.");
        return NULL;
    }
    return object;
}

cJSON* m_get_cjson_case_sensitive(cJSON *object, const char* item_key)
{
    return cJSON_GetObjectItemCaseSensitive(object, item_key);
}

cJSON* m_get_cjson(cJSON *object, const char* item_key)
{
    return cJSON_GetObjectItem(object, item_key);
}
char* m_get_cjson_string(cJSON *object)
{
    return cJSON_GetStringValue(object);
}
cJSON* m_get_cjson_array_item(cJSON *object, int index)
{
    return cJSON_GetArrayItem(object, index);
}

bool m_is_cjson_object(cJSON* object)
{
    return cJSON_IsObject(object);
}
bool m_is_cjson_number(cJSON* object)
{
    return cJSON_IsNumber(object);
}
bool m_is_cjson_array(cJSON* object)
{
    return cJSON_IsArray(object);
}

void m_print_preallocated_cjson(cJSON* object, char* output, int length, int fmt)
{
    cJSON_PrintPreallocated(object, output, length, fmt);
}
