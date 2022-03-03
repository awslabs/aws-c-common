#ifndef AWS_IOT_DEVICE_SDK_CPP_V2_JSON_CONVERTER_H
#define AWS_IOT_DEVICE_SDK_CPP_V2_JSON_CONVERTER_H

/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/common/allocator.h>
#include <aws/common/json/json_data.h>

void *aws_cJSON_alloc(size_t sz);
void aws_cJSON_free(void *ptr);

/**
 * Call to initialize the JSON module prior to calling "aws_json_*" functions.
 * @param allocator The allocator used to create and free cJSON objects.
 */
void aws_json_converter_init(struct aws_allocator *allocator);
/**
 * Call when finished with the JSON module to clean up JSON memory.
 */
void aws_json_converter_clean_up(void);

struct aws_json_node *aws_parse_json_from_string(char* string);
char *aws_convert_json_to_string(struct aws_json_node *node);

#endif // AWS_IOT_DEVICE_SDK_CPP_V2_JSON_CONVERTER_H
