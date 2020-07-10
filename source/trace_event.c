/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */
#include <aws/common/bus.h>
#include <aws/common/clock.h>
#include <aws/common/external/cJSON.h>
#include <aws/common/logging.h>
#include <aws/common/process.h>
#include <aws/common/string.h>
#include <aws/common/thread.h>
#include <aws/common/trace_event.h>
#include <errno.h>
/* Disable warnings with windows build */
#ifdef _MSC_VER
#    pragma warning(disable : C4996)
#    pragma warning(disable : C4100)
#    pragma
#endif

/*
 * Data structures
 */

struct trace_system {
    struct cJSON *root, *event_array;
    struct aws_bus bus;
    struct aws_allocator *allocator;
    uint64_t start_time;
    struct aws_string *filename;
    int time_unit;
};

struct aws_trace_event_metadata {
    /* should be B/E for same scope or S/F for outside of scope */
    char phase;
    /* name of the event */
    const char *name;
    /* category of the event */
    const char *category;
    /* timestamp in milliseconds */
    uint64_t timestamp;
    uint64_t thread_id;

    int process_id;

    int id;

    /* if args are enabled either args_1 or args_2 must be allocated */
    int num_args;

    int value[2];

    const char *value_name[2];
};

/*
 * Place holder to be added in later

    struct aws_trace_system_options{
        bool write_to_file;
        int time_units;
    };
 *
 */

static struct trace_system *s_trace;

/*
 * Private API
 */

/* function declaration to prevent compiler errors */
static void s_trace_event_listener(uint64_t address, const void *msg, void *user_data);

static void s_trace_system_write(void) {
    if (s_trace->time_unit == AWS_TIMESTAMP_NANOS) {
        AWS_FATAL_ASSERT(cJSON_AddStringToObject(s_trace->root, "displayTimeUnit", "ns"));
    }
    char *out = cJSON_Print((s_trace->root));
    AWS_FATAL_ASSERT(out);

    /* do not write out if strlen fails */
    char fn[s_trace->filename->len + 6];
    char *file_extension = ".json";
    strcpy(fn, aws_string_c_str(s_trace->filename));
    strncat(fn, file_extension, strlen(file_extension));

    FILE *fp;
    fp = fopen(fn, "w");
    /* Do not write if file cannot be opened */
    if (fp == NULL) {
        aws_translate_and_raise_io_error(errno);
        goto release_out;
    }
    fprintf(fp, "%s", out);
    fclose(fp);

release_out:
    aws_mem_release(s_trace->allocator, out);
}

static void s_trace_event_system_clean_up(void) {
    if (!s_trace) {
        return;
    }
    /* if bus was not initiated */
    if (!s_trace->bus.impl) {
        goto release_trace_event;
    }

    aws_bus_unsubscribe(&(s_trace->bus), 0, s_trace_event_listener, NULL);
    aws_bus_clean_up(&(s_trace->bus));

    if (s_trace->filename != NULL) {
        s_trace_system_write();
        aws_mem_release(s_trace->allocator, s_trace->filename);
    }
    cJSON_Delete(s_trace->root);

release_trace_event:
    aws_mem_release(s_trace->allocator, s_trace);
}

/* Add trace event meta data to JSON object when the message bus allows it */
static void s_trace_event_listener(uint64_t address, const void *msg, void *user_data) {
    struct aws_trace_event_metadata *trace_event_data = (struct aws_trace_event_metadata *)msg;

    cJSON *event = cJSON_CreateObject();

    AWS_FATAL_ASSERT(event);

    cJSON_AddItemToArray(s_trace->event_array, event);

    /* add more options later on */

    AWS_FATAL_ASSERT(cJSON_AddStringToObject(event, "cat", trace_event_data->category));
    AWS_FATAL_ASSERT(cJSON_AddStringToObject(event, "name", trace_event_data->name));

    /* If id is given add to cjson object */
    if (trace_event_data->id) {
        AWS_FATAL_ASSERT(cJSON_AddNumberToObject(event, "id", trace_event_data->id));
    }

    /* Fix for buffer overflow issue using char phase reference */
    char ph[2];
    strncat(ph, &(trace_event_data->phase), 1);

    AWS_FATAL_ASSERT(cJSON_AddStringToObject(event, "ph", ph));
    AWS_FATAL_ASSERT(cJSON_AddNumberToObject(event, "pid", trace_event_data->process_id));

    AWS_FATAL_ASSERT(cJSON_AddNumberToObject(event, "tid", trace_event_data->thread_id));

    AWS_FATAL_ASSERT(cJSON_AddNumberToObject(event, "ts", (double)trace_event_data->timestamp));

    // add args data if provided
    if (trace_event_data->num_args) { // if num args is greater than 0

        cJSON *args = cJSON_CreateObject();

        AWS_FATAL_ASSERT(args);

        cJSON_AddItemToObject(event, "args", args);
        for (int i = 0; i < trace_event_data->num_args; ++i) {
            AWS_FATAL_ASSERT(
                cJSON_AddNumberToObject(args, trace_event_data->value_name[i], trace_event_data->value[i]));
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
int aws_trace_system_init(struct aws_allocator *allocator, const char *filename) {
    if (allocator == NULL) {
        aws_raise_error(AWS_ERROR_INVALID_ARGUMENT);
        return AWS_OP_ERR;
    }

    s_trace = aws_mem_calloc(allocator, 1, sizeof(struct trace_system));
    if (!s_trace) {
        return AWS_OP_ERR;
    }
    s_trace->allocator = allocator;

    /* start the message bus */
    /* Add option to select sync vs async? */
    struct aws_bus_options options = {
        .allocator = s_trace->allocator,
        .policy = AWS_BUS_SYNC,
    };

    if (aws_bus_init(&(s_trace->bus), &options)) {
        goto error;
    }

    if (aws_bus_subscribe(&(s_trace->bus), 0, s_trace_event_listener, NULL)) {
        goto error;
    }

    s_trace->root = cJSON_CreateObject();

    AWS_FATAL_ASSERT(s_trace->root);
    s_trace->event_array = cJSON_CreateArray();
    AWS_FATAL_ASSERT(s_trace->event_array);

    cJSON_AddItemToObject(s_trace->root, "traceEvents", s_trace->event_array);

    /* Set starting time for program */
    if (aws_high_res_clock_get_ticks(&(s_trace->start_time))) {
        goto error;
    }

    /* allocate memory and enable writing out if filename is not null */
    if (filename != NULL) {
        s_trace->filename = aws_string_new_from_c_str(s_trace->allocator, filename);
        if (s_trace->filename == NULL) {
            goto error;
        }
    }

    return AWS_OP_SUCCESS;

error:
    aws_trace_system_clean_up();
    return AWS_OP_ERR;
}

int aws_trace_event(
    const char *category,
    const char *name,
    char phase,
    int value_1,
    const char *value_name_1,
    int value_2,
    const char *value_name_2) {

    /* set timestamps are in nanoseconds */
    uint64_t timestamp;

    if (aws_high_res_clock_get_ticks(&timestamp)) {
        return AWS_OP_ERR;
    }

    timestamp -= s_trace->start_time;
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

    trace_event_data.name = name;
    trace_event_data.category = category;
    /* Make thread id the event id for counter events */
    if (phase == EVENT_PHASE_COUNTER) {
        trace_event_data.id = thread_id;
    }

    /* addding args metadata */
    if (value_name_1 != NULL) {
        trace_event_data.num_args += 1;
        //! CHECK HOW TO FIX THIS
        trace_event_data.value[0] = value_1;
        trace_event_data.value_name[0] = value_name_1;

        /* initialize args_2 pointer if 2 values are given */
        if (value_name_2 != NULL) {
            trace_event_data.num_args += 1;
            trace_event_data.value[1] = value_2;
            trace_event_data.value_name[1] = value_name_2;
        }
    }

    /* send to the bus */
    if (aws_bus_send(&(s_trace->bus), 0, &trace_event_data, NULL)) {
        return AWS_OP_ERR;
    }
    return AWS_OP_SUCCESS;
}

void *aws_trace_event_get_root() {
    return s_trace->root;
}
