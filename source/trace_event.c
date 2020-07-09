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
#include <errno.h>
/* Disable warnings with windows build */
#ifdef _MSC_VER
#    pragma warning(disable : C4996)
#    pragma warning(disable : C4100)
#    pragma
#endif

/* use on external cJSON function for error checking */
#define ERROR_CHECK(result, error_type)                                                                                \
    do {                                                                                                               \
        if (!result) {                                                                                                 \
            aws_raise_error(error_type);                                                                               \
            AWS_FATAL_ASSERT(0 && "trace failure");                                                                    \
        }                                                                                                              \
    } while (0)

/*
 * Data structures
 */

struct aws_trace_event {
    struct cJSON *root, *event_array;
    struct aws_bus bus;
    struct aws_allocator *allocator;
};

struct aws_trace_event *trace_event;

/*
 * Place holder to be added in later

    struct aws_trace_system_options{
        bool write_to_file;
        int time_units;
    };
 *
 */
// uint64_t listener_id = 1;
uint64_t start_time;
// bool write_to_file;
char *filename_out;
const int time_unit = AWS_TIMESTAMP_MICROS;

struct aws_trace_event_metadata_counter {
    int value;
    char value_name[15];
};

struct aws_trace_event_metadata {
    /* should be B/E for same scope or S/F for outside of scope */
    char phase;
    /* name of the event */
    char name[15];
    /* category of the event */
    char category[15];
    /* timestamp in milliseconds */
    uint64_t timestamp;
    uint64_t thread_id;
    int process_id;
    /* Pointer to counter data if provided */
    struct aws_trace_event_metadata_counter *counter_data;
};

/*
 * Private API
 */

void aws_trace_event_listener(uint64_t address, const void *msg, void *user_data);

void aws_trace_system_write() {
    if (time_unit == AWS_TIMESTAMP_NANOS) {
        if (cJSON_AddStringToObject(trace_event->root, "displayTimeUnit", "ns") == NULL) {
            aws_raise_error(AWS_ERROR_OOM);
            AWS_FATAL_ASSERT(0 && "trace failure");
        }
    }
    char *out = cJSON_Print((trace_event->root));
    if (out == NULL) {
        aws_raise_error(AWS_ERROR_OOM);
        AWS_FATAL_ASSERT(0 && "trace failure");
    }
    FILE *fp;
    char fn[strlen(filename_out) + 6];

    strcpy(fn, filename_out);
    strncat(fn, ".json", 6);

    fp = fopen(fn, "w");
    /* Do not write if file cannot be opened */
    if (fp == NULL) {
        aws_translate_and_raise_io_error(errno);
        goto release_out;
    }
    fprintf(fp, "%s", out);
    fclose(fp);

release_out:
    aws_mem_release(trace_event->allocator, out);
}

void s_trace_event_system_clean_up() {
    if (!trace_event) {
        return;
    }
    /* if bus was not initiated */
    if (!trace_event->bus.impl) {
        goto release_trace_event;
    }

    aws_bus_unsubscribe(&(trace_event->bus), 0, aws_trace_event_listener, NULL);
    aws_bus_clean_up(&(trace_event->bus));

    if (filename_out != NULL) {
        aws_trace_system_write();
        aws_mem_release(trace_event->allocator, filename_out);
    }
    cJSON_Delete(trace_event->root);

release_trace_event:
    aws_mem_release(trace_event->allocator, trace_event);
}

/* Free memory allocated if counter is used */
void aws_trace_event_destroy(void *payload) {
    struct aws_trace_event_metadata *trace_event_data = (struct aws_trace_event_metadata *)payload;
    if (trace_event_data->phase == EVENT_PHASE_COUNTER) {
        aws_mem_release(trace_event->allocator, trace_event_data->counter_data);
    }
}

/* Add trace event meta data to JSON object when the message bus allows it */
void aws_trace_event_listener(uint64_t address, const void *msg, void *user_data) {
    struct aws_trace_event_metadata *trace_event_data = (struct aws_trace_event_metadata *)msg;
    if (trace_event_data == NULL) {
        /* CHECK THAT THIS IS THE RIGHT ERROR CODE */
        aws_raise_error(AWS_ERROR_INVALID_ARGUMENT);
        s_trace_event_system_clean_up();
        AWS_FATAL_ASSERT(0 && "trace failure");
    }
    cJSON *event = cJSON_CreateObject();

    ERROR_CHECK(event, AWS_ERROR_OOM);

    cJSON_AddItemToArray(trace_event->event_array, event);

    /* add options for args later on, will initially be empty for now */
    // cJSON_AddItemToObject(event, "args", cJSON_CreateObject());

    /* add more options later on */

    ERROR_CHECK(cJSON_AddStringToObject(event, "cat", trace_event_data->category), AWS_ERROR_OOM);
    ERROR_CHECK(cJSON_AddStringToObject(event, "name", trace_event_data->name), AWS_ERROR_OOM);

    /* Fix for buffer overflow issue using char phase reference */
    char ph[2];
    strncat(ph, &(trace_event_data->phase), 1);

    ERROR_CHECK(cJSON_AddStringToObject(event, "ph", ph), AWS_ERROR_OOM);
    ERROR_CHECK(cJSON_AddNumberToObject(event, "pid", trace_event_data->process_id), AWS_ERROR_OOM);

    ERROR_CHECK(cJSON_AddNumberToObject(event, "tid", trace_event_data->thread_id), AWS_ERROR_OOM);

    ERROR_CHECK(cJSON_AddNumberToObject(event, "ts", (double)trace_event_data->timestamp), AWS_ERROR_OOM);

    // add counter data if provided
    if (trace_event_data->phase == EVENT_PHASE_COUNTER) {
        if (trace_event_data->counter_data != NULL) {

            cJSON *args = cJSON_CreateObject();

            ERROR_CHECK(args, AWS_ERROR_OOM);

            cJSON_AddItemToObject(event, "args", args);

            ERROR_CHECK(
                cJSON_AddNumberToObject(
                    args, trace_event_data->counter_data->value_name, trace_event_data->counter_data->value),
                AWS_ERROR_OOM);
        }
    }
}

/*
 * Public API
 */

void aws_trace_system_clean_up(void) {
    s_trace_event_system_clean_up();
}

/* starts the message bus and initializes the JSON root, and the event array for storing metadata */
int aws_trace_system_init(const char *filename, struct aws_allocator *allocator) {
    if (allocator == NULL) {
        aws_raise_error(AWS_ERROR_INVALID_ARGUMENT);
        return AWS_OP_ERR;
    }

    trace_event = aws_mem_calloc(allocator, 1, sizeof(struct aws_trace_event));
    trace_event->allocator = allocator;

    /* start the message bus */
    /* Add option to select sync vs async? */
    struct aws_bus_options options = {
        .allocator = trace_event->allocator,
        .policy = AWS_BUS_SYNC,
    };

    if (aws_bus_init(&(trace_event->bus), &options)) {
        /* error occurs when bus->impl is not implemented */
        aws_raise_error(AWS_ERROR_UNIMPLEMENTED);
        goto error;
    }

    if (aws_bus_subscribe(&(trace_event->bus), 0, aws_trace_event_listener, NULL)) {
        /* error occurs when bus's list of subscribers does not find or creater a spot for listener */
        aws_raise_error(AWS_ERROR_LIST_EMPTY);
        goto error;
    }

    trace_event->root = cJSON_CreateObject();

    ERROR_CHECK(trace_event->root, AWS_ERROR_OOM);

    trace_event->event_array = cJSON_CreateArray();
    ERROR_CHECK(trace_event->event_array, AWS_ERROR_OOM);

    cJSON_AddItemToObject(trace_event->root, "traceEvents", trace_event->event_array);

    /* maybe kill program entirely when this happens */
    /* Set starting time for program */
    if (aws_high_res_clock_get_ticks(&start_time)) {
        aws_raise_error(AWS_ERROR_CLOCK_FAILURE);
        goto error;
    }

    if (filename != NULL) {
        filename_out = aws_mem_acquire(trace_event->allocator, strlen(filename) + 1);
        strcpy(filename_out, filename);
    }

    return AWS_OP_SUCCESS;

error:
    aws_trace_system_clean_up();
    return AWS_OP_ERR;
}

int aws_trace_event(const char *category, const char *name, char phase, int value, const char *value_name) {
    /* set timestamps are in nanoseconds */
    uint64_t timestamp;

    if (aws_high_res_clock_get_ticks(&timestamp)) {
        aws_raise_error(AWS_ERROR_CLOCK_FAILURE);
        return AWS_OP_ERR;
    }

    timestamp -= start_time;
    /* convert timestamps to tracing format of microseconds */
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

    /* addding counter metadata */
    if (phase == EVENT_PHASE_COUNTER) {
        trace_event_data.counter_data =
            aws_mem_calloc(trace_event->allocator, 1, sizeof(struct aws_trace_event_metadata_counter));
        trace_event_data.counter_data->value = value;
        strncpy(trace_event_data.counter_data->value_name, value_name, 14);
    }

    /* send to the bus */
    if (aws_bus_send(&(trace_event->bus), 0, &trace_event_data, aws_trace_event_destroy)) {
        if (!AWS_IS_ZEROED(trace_event_data.counter_data)) {
            aws_mem_release(trace_event->allocator, trace_event_data.counter_data);
        }
        return AWS_OP_ERR;
    }
    return AWS_OP_SUCCESS;
}

void *aws_trace_event_get_root() {
    return trace_event->root;
}
