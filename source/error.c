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
#include <stdio.h>
#include <stdlib.h>

static AWS_THREAD_LOCAL int tl_last_error = 0;

static aws_error_handler_fn *s_global_handler = NULL;
static void *s_global_error_context = NULL;

static AWS_THREAD_LOCAL aws_error_handler_fn *tl_thread_handler = NULL;
AWS_THREAD_LOCAL void *tl_thread_handler_context = NULL;

#ifndef AWS_MAX_ERROR_SLOTS
#    define AWS_MAX_ERROR_SLOTS 16
#endif

/* Since slot size is 00000100 00000000, to divide, we need to shift right by 10
 * bits to find the slot, and to find the modulus, we use a binary and with
 * 00000011 11111111 to find the index in that slot. The next three values
 * define those constants */
#define AWS_ERROR_SLOT_SIZE 0x0400
#define SLOT_DIV_SHIFT 0x0A
#define SLOT_MASK 0x03FF

static const int MAX_ERROR_CODE = AWS_ERROR_SLOT_SIZE * AWS_MAX_ERROR_SLOTS;

static const struct aws_error_info_list *volatile ERROR_SLOTS[AWS_MAX_ERROR_SLOTS] = {0};

int aws_last_error(void) {
    return tl_last_error;
}

static const struct aws_error_info *get_error_by_code(int err) {
    if (err >= MAX_ERROR_CODE || err < 0) {
        return NULL;
    }

    int slot_index = err >> SLOT_DIV_SHIFT;
    int error_index = err & SLOT_MASK;

    const struct aws_error_info_list *error_slot = ERROR_SLOTS[slot_index];

    if (!error_slot || error_index >= error_slot->count) {
        return NULL;
    }

    return &error_slot->error_list[error_index];
}

const char *aws_error_str(int err) {
    const struct aws_error_info *error_info = get_error_by_code(err);

    if (error_info) {
        return error_info->error_str;
    }

    return "Unknown Error Code";
}

const char *aws_error_lib_name(int err) {
    const struct aws_error_info *error_info = get_error_by_code(err);

    if (error_info) {
        return error_info->lib_name;
    }

    return "Unknown Error Code";
}

const char *aws_error_debug_str(int err) {
    const struct aws_error_info *error_info = get_error_by_code(err);

    if (error_info) {
        return error_info->formatted_name;
    }

    return "Unknown Error Code";
}

void aws_raise_error_private(int err) {
    tl_last_error = err;

    if (tl_thread_handler) {
        tl_thread_handler(tl_last_error, tl_thread_handler_context);
    } else if (s_global_handler) {
        s_global_handler(tl_last_error, s_global_error_context);
    }
}

void aws_reset_error(void) {
    tl_last_error = 0;
}

void aws_restore_error(int err) {
    tl_last_error = err;
}

aws_error_handler_fn *aws_set_global_error_handler_fn(aws_error_handler_fn *handler, void *ctx) {
    aws_error_handler_fn *old_handler = s_global_handler;
    s_global_handler = handler;
    s_global_error_context = ctx;

    return old_handler;
}

aws_error_handler_fn *aws_set_thread_local_error_handler_fn(aws_error_handler_fn *handler, void *ctx) {
    aws_error_handler_fn *old_handler = tl_thread_handler;
    tl_thread_handler = handler;
    tl_thread_handler_context = ctx;

    return old_handler;
}

void aws_register_error_info(const struct aws_error_info_list *error_info) {
    /*
     * We're not so worried about these asserts being removed in an NDEBUG build
     * - we'll either segfault immediately (for the first two) or for the count
     * assert, the registration will be ineffective.
     */
    assert(error_info);
    assert(error_info->error_list);
    assert(error_info->count);

    int min_range = error_info->error_list[0].error_code;

    int slot_index = min_range >> SLOT_DIV_SHIFT;

    assert(slot_index < AWS_MAX_ERROR_SLOTS && slot_index >= 0);

    if (slot_index >= AWS_MAX_ERROR_SLOTS || slot_index < 0) {
        /* This is an NDEBUG build apparently. Kill the process rather than
         * corrupting heap. */
        fprintf(stderr, "Bad error slot index 0x%016x\n", slot_index);
        abort();
    }

    ERROR_SLOTS[slot_index] = error_info;
}
