#ifndef AWS_COMMON_JSON_H
#define AWS_COMMON_JSON_H

/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/common/json/external/cJSON.h>
#include <aws/common/thread.h>

struct aws_allocator *s_json_module_allocator;
bool s_json_module_initialized;

void *s_cJSON_alloc(size_t sz);
void s_cJSON_free(void *ptr);
void s_json_init(struct aws_allocator *allocator);
void s_json_clean_up(void);


struct aws_json_parse_credentials_from_json_doc_options {
    const char *access_key_id_name;
    const char *secrete_access_key_name;
    const char *token_name;
    const char *expiration_name;
    bool token_required;
    bool expiration_required;
};
struct aws_json_parse_credentials_from_json_doc_results {
    char *access_key_id;
    char *secret_access_key;
    char *token;
    char *creds_expiration;
    uint64_t expiration_timepoint_in_seconds;
};
struct aws_json_parse_credentials_from_json_doc_results s_json_parse_credentials_from_cjson_object(
    struct cJSON *document_root,
    const struct aws_json_parse_credentials_from_json_doc_options *options);

cJSON *m_get_cjson_if_valid (cJSON *root, const char* name, const char* logName);


struct cJSON *m_create_cjson(void);
void m_add_item_to_cjson(cJSON *object, const char* item_key, cJSON *item_value);
bool m_create_and_add_cjson(cJSON *object, const char* item_key, cJSON* output);
bool m_add_string_to_cjson(cJSON *object, const char* item_key, const char* item_value);
bool m_add_number_to_cjson(cJSON *object, const char* item_key, const double item_value);
struct cJSON *m_create_cjson_array(void);
bool m_create_and_add_cjson_array(cJSON *object, const char* item_key, cJSON* output);
void m_add_item_to_cjson_array(cJSON *array, cJSON* item_value);
cJSON* m_create_cjson_number(const double item_value);
cJSON* m_create_cjson_string(const char* item_value);
char* m_print_unformatted_cjson(cJSON *object);
void m_delete_cjson(cJSON *object);
void m_free_cjson(cJSON *object);

cJSON* m_parse_cjson(const char* object);
cJSON* m_get_cjson_case_sensitive(cJSON *object, const char* item_key);
cJSON* m_get_cjson(cJSON *object, const char* item_key);
char* m_get_cjson_string(cJSON *object);
cJSON* m_get_cjson_array_item(cJSON *object, int index);

bool m_is_cjson_object(cJSON* object);
bool m_is_cjson_number(cJSON* object);
bool m_is_cjson_array(cJSON* object);

void m_print_preallocated_cjson(cJSON* object, char* output, int length, int fmt);

#endif // AWS_COMMON_JSON_H
