#ifndef AWS_COMMON_JSON_H
#define AWS_COMMON_JSON_H

/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/common/json/external/cJSON.h>
#include <aws/common/thread.h>

void *aws_cJSON_alloc(size_t sz);
void aws_cJSON_free(void *ptr);

/**
 * Call to initialize the JSON module prior to calling "aws_json_*" functions.
 * @param allocator The allocator used to create and free cJSON objects.
 */
void aws_json_init(struct aws_allocator *allocator);
/**
 * Call when finished with the JSON module to clean up JSON memory.
 */
void aws_json_clean_up(void);

/**
 * The options that can be passed to the aws_json_parse_credentials_from_cjson function.
 * Required for the aws_json_parse_credentials_from_cjson function.
 */
struct aws_json_parse_credentials_options {
    const char *access_key_id_name;
    const char *secrete_access_key_name;
    const char *token_name;
    const char *expiration_name;
    bool token_required;
    bool expiration_required;
};
/**
 * All of the credentials extracted from the cJSON document root passed into the
 * aws_json_parse_credentials_from_cjson function.
 */
struct aws_json_parse_credentials_results {
    char *access_key_id;
    char *secret_access_key;
    char *token;
    char *creds_expiration;
    uint64_t expiration_timepoint_in_seconds;
};
/**
 * Parses a cJSON object (expected document root) for credentials. Used to correctly parse and extract response
 * data from JSON documents sent by AWS servers.
 * @param document_root The cJSON document root
 * @param options The options to use when parsing the document root
 * @return aws_json_parse_credentials_result struct containing extracted credentials
 */
struct aws_json_parse_credentials_results aws_json_parse_credentials_from_cjson(
    struct cJSON *document_root,
    const struct aws_json_parse_credentials_options *options);

/**
 * Creates a new cJSON object and returns a pointer to it
 * @return A pointer to a new cJSON object
 */
struct cJSON *aws_json_create_cjson(void);
/**
 * Creates a new cJSON object, validates its creation, and adds it to the passed-in cJSON object.
 * Use the "output" pointer argument to get a reference to the newly created cJSON object.
 * @param object The cJSON object you want to add the new cJSON object to.
 * @param item_key The key to place the new cJSON object at.
 * @param output The newly created cJSON object.
 * @return Returns true if creation and addition was successful.
 */
bool aws_json_create_and_add_cjson(cJSON *object, const char *item_key, cJSON *output);
/**
 * Creates a new cJSON array and returns a pointer to it
 * @return A pointer to a new cJSON array
 */
struct cJSON *aws_json_create_cjson_array(void);
/**
 * Creates a new cJSON array, validates its creation, and adds it to the passed-in cJSON object.
 * Use the "output" pointer argument to get a reference to the newly created cJSON array.
 * @param object The cJSON object you want to add the new cJSON array to.
 * @param item_key The key to place the new cJSON array at.
 * @param output The newly created cJSON array.
 * @return Returns true if creation and addition was successful.
 */
bool aws_json_create_and_add_cjson_array(cJSON *object, const char *item_key, cJSON *output);
/**
 * Creates a new cJSON number object and returns a pointer to it.
 * @param item_value The number to be stored in the cJSON number object.
 * @return A pointer to the new cJSON number object.
 */
cJSON *aws_json_create_cjson_number(const double item_value);
/**
 * Creates a new cJSON string object and returns a pointer to it.
 * @param item_value The string to be stored in the cJSON string object.
 * @return A pointer to the new cJSON string object.
 */
cJSON *aws_json_create_cjson_string(const char *item_value);

/**
 * Parses a string containing a JSON document and returns the root JSON element as a cJSON object.
 * @param string The string containing the JSON document.
 * @return A pointer to the cJSON object created from the JSON document, or null if parsing fails.
 */
cJSON *aws_json_parse_cjson_from_string(const char *string);

/**
 * Adds a cJSON object (item_value) to another cJSON object (object) at the given key (item_key).
 * @param object The cJSON object you want to add a cJSON object to.
 * @param item_key The key name you want to place the cJSON object at.
 * @param item_value The cJSON object you want to add.
 */
void aws_json_add_item_to_cjson(cJSON *object, const char *item_key, cJSON *item_value);
/**
 * Adds a cJSON object (item_value) to a cJSON array (object) at the end of the cJSON array.
 * @param array The cJSON array you want to add a cJSON object to.
 * @param item_value The cJSON object you want to add.
 */
void aws_json_add_item_to_cjson_array(cJSON *array, cJSON *item_value);
/**
 * Adds a cJSON string to the cJSON object at the given key.
 * @param object The cJSON object you want to add a cJSON string to.
 * @param item_key The key name you want to place the cJSON sting at.
 * @param item_value The string you want to add.
 * @return True if adding the cJSON string is successful, false otherwise.
 */
bool aws_json_add_string_to_cjson(cJSON *object, const char *item_key, const char *item_value);
/**
 * Adds a cJSON number to the cJSON object at the given key.
 * @param object The cJSON object you want to add a cJSON number to.
 * @param item_key The key name you want to place the cJSON number at.
 * @param item_value The number you want to add.
 * @return True if adding the cJSON number is successful, false otherwise.
 */
bool aws_json_add_number_to_cjson(cJSON *object, const char *item_key, const double item_value);

/**
 * Returns the cJSON item in the passed-in cJSON item at the given key.
 * @param object The cJSON item that contains the cJSON item at the key.
 * @param item_key The key name where the cJSON item is placed.
 * @return A pointer to the cJSON item at the given key if it exists, otherwise null.
 */
cJSON *aws_json_get_cjson(cJSON *object, const char *item_key);
/**
 * Returns the cJSON item in the passed-in cJSON item at the given key. Will validate the existence of
 * the cJSON key and will print a log error if the cJSON item does not exist.
 * @param object The cJSON item that contains the cJSON item at the key.
 * @param item_key The key name where the cJSON is placed.
 * @param log_key_name The name to show in the error log if the key does not exist in the cJSON item.
 * @return A pointer to the cJSON item at the given key if it exists, otherwise null.
 */
cJSON *aws_json_get_cjson_with_validate(cJSON *object, const char *item_key, const char *log_key_name);
/**
 * Returns the cJSON item in the passed-in cJSON item at the given case-sensitive key.
 * @param object The cJSON item that contains the cJSON item at the key.
 * @param item_key The case sensitive key name where teh cJSON item is placed.
 * @return A pointer to the cJSON item at the given key if it exists, otherwise null.
 */
cJSON *aws_json_get_cjson_case_sensitive(cJSON *object, const char *item_key);
/**
 * Gets the string value from the cJSON object and returns it.
 * @param object The cJSON object containing the string value.
 * @return The string value in the cJSON object.
 */
char *aws_json_get_cjson_string(cJSON *object);
/**
 * Returns the cJSON object at the given array index, if it exists.
 * @param object The cJSON array.
 * @param index The index in the cJSON array.
 * @return A pointer to the cJSON item at the given index if it exists, otherwise null.
 */
cJSON *aws_json_get_cjson_array_item(cJSON *object, int index);

/**
 * Checks whether the cJSON pointer is a cJSON object.
 * @param object The cJSON pointer to check.
 * @return True if the cJSON pointer is a cJSON object, otherwise false.
 */
bool aws_json_is_cjson_object(cJSON *object);
/**
 * Checks whether the cJSON pointer is a cJSON number.
 * @param object The cJSON pointer to check.
 * @return True if the cJSON pointer is a cJSON number, otherwise false.
 */
bool aws_json_is_cjson_number(cJSON *object);
/**
 * Checks whether the cJSON pointer is a cJSON array.
 * @param object The cJSON pointer to check.
 * @return True if the cJSON pointer is a cJSON array, otherwise false.
 */
bool aws_json_is_cjson_array(cJSON *object);

/**
 * Returns a string containing the unformatted print of a cJSON object. Can be used to get the JSON string from a
 * cJSON document root.
 * @param object The cJSON object to print.
 * @return An unformatted JSON string of the cJSON object.
 */
char *aws_json_print_unformatted_cjson(cJSON *object);
/**
 * Stores a string containing the unformatted print of a cJSON object into the given string as output.
 * @param object The cJSON object to print.
 * @param output The string to store the print output in.
 * @param length The length of the string.
 * @param fmt Whether to format the output (0 = false, 1 = true).
 */
void aws_json_print_preallocated_cjson(cJSON *object, char *output, int length, int fmt);

/**
 * Deletes the cJSON object
 * @param object The cJSON object to delete.
 */
void aws_json_delete_cjson(cJSON *object);
/**
 * Frees the cJSON object.
 * @param object The cJSON object to free.
 */
void aws_json_free_cjson(cJSON *object);

#endif // AWS_COMMON_JSON_H
