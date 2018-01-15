/*
* Copyright 2010-2018 Amazon.com, Inc. or its affiliates. All Rights Reserved.
*
* Licensed under the Apache License, Version 2.0 (the "License").
* You may not use this file except in compliance with the License.
* A copy of the License is located at
*
*  http://aws.amazon.com/apache2.0
*
* or in the "license" file accompanying this file. This file is distributed
* on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
* express or implied. See the License for the specific language governing
* permissions and limitations under the License.
*/

#include <aws/common/error.h>
#include <aws/common/common.h>
#include <assert.h>

AWS_THREAD_LOCAL int last_error = 0;

static aws_error_handler global_handler = NULL;
static void *global_error_context = NULL;

AWS_THREAD_LOCAL aws_error_handler thread_handler = NULL;
AWS_THREAD_LOCAL void *thread_handler_context = NULL;

#ifndef AWS_MAX_ERROR_SLOTS
#define AWS_MAX_ERROR_SLOTS 10
#endif

#define AWS_ERROR_SLOT_SIZE 1000

static volatile const struct aws_error_info_list *error_slots[AWS_MAX_ERROR_SLOTS] = { 0 };

int aws_last_error(void) {
    return last_error;
}

static const struct aws_error_info *get_error_by_code(int err) {
    if(err >= AWS_MAX_ERROR_SLOTS * AWS_ERROR_SLOT_SIZE) {
        return NULL;
    }

    int slot_index = err / AWS_ERROR_SLOT_SIZE;
    int error_index = err % AWS_ERROR_SLOT_SIZE;

    volatile const struct aws_error_info_list *error_slot = error_slots[slot_index];

    if(!error_slot || error_index >= error_slot->count) {
        return NULL;
    }

    return &error_slot->error_list[error_index];
}

const char *aws_error_str(int err) {
    assert(err >= 0);

    const struct aws_error_info *error_info = get_error_by_code(err);

    if(error_info) {
        return error_info->error_str;
    }

    return "Unknown Error Code";
}

const char *aws_error_lib_name(int err) {
    assert(err >= 0);

    const struct aws_error_info *error_info = get_error_by_code(err);

    if(error_info) {
        return error_info->lib_name;
    }

    return "Unknown Error Code";
}

const char *aws_error_debug_str(int err) {
    assert(err >= 0);

    const struct aws_error_info *error_info = get_error_by_code(err);

    if(error_info) {
        return error_info->formatted_name;
    }

    return "Unknown Error Code";
}

void aws_raise_error(int err) {
    last_error = err;

    if(thread_handler) {
        thread_handler(last_error, thread_handler_context);
    }
    else if(global_handler) {
        global_handler(last_error, global_error_context);
    }

}

void aws_reset_error(void) {
    last_error = 0;
}

void aws_restore_error(int err) {
    last_error = err;
}

void aws_set_global_error_handler_fn(aws_error_handler handler, void *ctx) {
    global_handler = handler;
    global_error_context = ctx;
}

void aws_set_thread_local_error_handler_fn(aws_error_handler handler, void *ctx) {
    thread_handler = handler;
    thread_handler_context = ctx;
}

void aws_register_error_info(const struct aws_error_info_list *error_info) {
    assert(error_info);
    assert(error_info->error_list);
    assert(error_info->count);

    int min_range = error_info->error_list[0].error_code;

    int slot_index = min_range / AWS_ERROR_SLOT_SIZE;
    assert(slot_index < AWS_MAX_ERROR_SLOTS);


    error_slots[slot_index] = error_info;
}
