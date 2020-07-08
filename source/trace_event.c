/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */
#include <aws/common/bus.h>
#include <aws/common/clock.h>
#include <aws/common/external/cJSON.h>
#include <aws/common/logging.h>
#include <aws/common/process.h>
#include <aws/common/thread.h>
#include <aws/common/trace_event.h>

struct aws_trace_event *trace_event;
// uint64_t listener_id = 1;
uint64_t start_time;

/*
 * Private API
 */

#define ERROR_CHECK(result)                                                                                            \
    do {                                                                                                               \
        if (!result) {                                                                                                 \
            AWS_FATAL_ASSERT(0 && "trace failure")                                                                     \
        }                                                                                                              \
    } while (0)

struct aws_trace_event {
    struct cJSON *root, *event_array;
    struct aws_bus bus;
    struct aws_allocator *allocator;
};

/* Add trace event meta data to JSON object when the message bus allows it */
void aws_trace_event_listener(uint64_t address, const void *msg, void *user_data) {
    struct aws_trace_event_metadata *trace_event_data = (struct aws_trace_event_metadata *)msg;
    if (trace_event_data == NULL) {
        aws_raise_error(AWS_ERROR_OOM);
    }
    cJSON *event = cJSON_CreateObject();
    if (event == NULL) {
        aws_raise_error(AWS_ERROR_OOM);
    }

    cJSON_AddItemToArray(trace_event->event_array, event);

    /* add options for args later on, will initially be empty for now */
    cJSON_AddItemToObject(event, "args", cJSON_CreateObject());

    /* add more options later on */
    if (cJSON_AddStringToObject(event, "cat", trace_event_data->category) == NULL) {
        aws_raise_error(AWS_ERROR_OOM);
    }
    if (cJSON_AddStringToObject(event, "name", trace_event_data->name) == NULL) {
        aws_raise_error(AWS_ERROR_OOM);
    }
    /* Fix for buffer overflow issue using char phase reference */
    char ph[2];
    strncat(ph, &(trace_event_data->phase), 1);
    if (cJSON_AddStringToObject(event, "ph", ph) == NULL) {
        aws_raise_error(AWS_ERROR_OOM);
    }
    if (cJSON_AddNumberToObject(event, "pid", trace_event_data->process_id) == NULL) {
        aws_raise_error(AWS_ERROR_OOM);
    }
    if (cJSON_AddNumberToObject(event, "tid", trace_event_data->thread_id)) {
        aws_raise_error(AWS_ERROR_OOM);
    }
    if (cJSON_AddNumberToObject(event, "ts", (double)trace_event_data->timestamp)) {
        aws_raise_error(AWS_ERROR_OOM);
    }
}

/* Destructor of trace event metadata sent through the bus */
void aws_trace_event_destroy(void *payload) {}

void aws_trace_system_write(int time_unit, const char *filename) {
    if (time_unit) {
        if (cJSON_AddStringToObject(trace_event->root, "displayTimeUnit", "ns") == NULL) {
            aws_raise_error(AWS_ERROR_OOM);
        }
    }
    char *out = cJSON_Print((trace_event->root));
    if (out == NULL) {
        aws_raise_error(AWS_ERROR_OOM);
    }
    FILE *fp;
    char fn[strlen(filename) + 6];

    strcpy(fn, filename);
    strncat(fn, ".json", 6);

    fp = fopen(fn, "w");
    if (fp == NULL) {
        aws_raise_error(AWS_ERROR_OOM);
    }
    fprintf(fp, "%s", out);
    fclose(fp);
    aws_mem_release(trace_event->allocator, out);
}

/*
 * Public API
 */

/* starts the message bus and initializes the JSON root, and the event array for storing metadata */
int aws_trace_system_init(struct aws_allocator *allocator) {
    if (allocator == NULL) {
        return AWS_OP_ERR;
    }
    trace_event = aws_mem_acquire(allocator, sizeof(struct aws_trace_event));
    trace_event->allocator = allocator;

    trace_event->root = cJSON_CreateObject();
    if (trace_event->root == NULL) {
        /* Error code may be changed on review */
        aws_raise_error(AWS_ERROR_OOM);
    }
    trace_event->event_array = cJSON_CreateArray();
    if (trace_event->event_array == NULL) {
        aws_raise_error(AWS_ERROR_OOM);
    }
    cJSON_AddItemToObject(trace_event->root, "traceEvents", trace_event->event_array);

    if (aws_high_res_clock_get_ticks(&start_time)) {
        return AWS_OP_ERR;
    }

    /* start the message bus */
    /* Add option to select sync vs async? */
    struct aws_bus_options options = {
        .allocator = allocator,
        .policy = AWS_BUS_SYNC,
    };

    if (aws_bus_init(&(trace_event->bus), &options)) {
        return AWS_OP_ERR;
    }

    if (aws_bus_subscribe(&(trace_event->bus), 0, aws_trace_event_listener, NULL)) {
        return AWS_OP_ERR;
    }

    return AWS_OP_SUCCESS;
}

void aws_trace_system_clean_up(int code, int time_unit, const char *filename) {
    aws_bus_unsubscribe(&(trace_event->bus), 0, aws_trace_event_listener, NULL);
    aws_bus_clean_up(&(trace_event->bus));

    if (code && filename != NULL) {
        aws_trace_system_write(time_unit, filename);
    }
    cJSON_Delete(trace_event->root);
    aws_mem_release(trace_event->allocator, trace_event);
}

int aws_trace_event_new(const char *category, const char *name, char phase) {
    /* set timestamp in milliseconds */
    uint64_t timestamp;
    if (aws_high_res_clock_get_ticks(&timestamp)) {
        return AWS_OP_ERR;
    }
    timestamp -= start_time;

    timestamp = aws_timestamp_convert(timestamp, AWS_TIMESTAMP_NANOS, AWS_TIMESTAMP_MICROS, 0);

    /* get calling thread and process ids */
    uint64_t thread_id = (uint64_t)aws_thread_current_thread_id();
    int process_id = aws_get_pid();

    struct aws_trace_event_metadata trace_event_data = {
        .phase = phase,
        .timestamp = timestamp,
        .thread_id = thread_id,
        .process_id = process_id,
    };

    strncpy(trace_event_data.name, name, 14);
    strncpy(trace_event_data.category, category, 14);

    /* send to the bus */
    if (aws_bus_send(&(trace_event->bus), 0, &trace_event_data, aws_trace_event_destroy)) {
        return AWS_OP_ERR;
    }
    return AWS_OP_SUCCESS;
}

void *aws_trace_event_get_root() {
    return trace_event->root;
}
