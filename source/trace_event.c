/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */
#include <aws/common/bus.h>
#include <aws/common/clock.h>
#include <aws/common/logging.h>
#include <aws/common/process.h>
#include <aws/common/thread.h>
#include <aws/common/trace_event.h>
#include <errno.h>
#include <inttypes.h>
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
    struct aws_bus bus;
    struct aws_allocator *allocator;
    uint64_t start_time;
    enum aws_trace_system_time_display_unit time_unit;
    FILE *fp;
    int num_traces;
};

enum trace_event_args {
    NO_ARG,       // 0
    INT_ARG_1,    // 1
    INT_ARG_2,    // 2
    STRING_ARG_1, // 3
    STRING_ARG_2  // 4
};

struct aws_trace_event_data {
    /* should be B/E for duration, I for instant, C for counter, and M for metadata */
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

    enum trace_event_args args;

    int value[2];

    const char *value_name[2];

    const char *value_str[2];
};

static struct trace_system *s_trace;

/*
 * Private API
 */

/* A listener that writes to the JSON file */
static void s_trace_event_write(uint64_t address, const void *msg, void *user_data) {
    struct aws_trace_event_data *trace_event_data = (struct aws_trace_event_data *)msg;
    if (s_trace == NULL) {
        return;
    }
    if (s_trace->fp == NULL) {
        return;
    }
    s_trace->num_traces += 1;

    switch (trace_event_data->args) {
        case NO_ARG:
            fprintf(
                s_trace->fp,
                "{\"cat\":\"%s\",\"name\":\"%s\",\"ph\":\"%c\",\"pid\":%i,\"tid\":%llu,\"ts\":%llu},\n",
                trace_event_data->category,
                trace_event_data->name,
                trace_event_data->phase,
                trace_event_data->process_id,
                (unsigned long long)trace_event_data->thread_id,
                (unsigned long long)trace_event_data->timestamp);
            break;
        case INT_ARG_1:
            fprintf(
                s_trace->fp,
                "{\"cat\":\"%s\",\"name\":\"%s\",\"ph\":\"%c\",\"pid\":%i,\"tid\":%llu,\"ts\":%llu,\"args\":{\"%s\":%i}"
                "},"
                "\n",
                trace_event_data->category,
                trace_event_data->name,
                trace_event_data->phase,
                trace_event_data->process_id,
                (unsigned long long)trace_event_data->thread_id,
                (unsigned long long)trace_event_data->timestamp,
                trace_event_data->value_name[0],
                trace_event_data->value[0]);
            break;
        case INT_ARG_2:
            fprintf(
                s_trace->fp,
                "{\"cat\":\"%s\",\"name\":\"%s\",\"ph\":\"%c\",\"pid\":%i,\"tid\":%llu,\"ts\":%llu,\"args\":{\"%s\":%i,"
                "\"%s\":%i}},\n",
                trace_event_data->category,
                trace_event_data->name,
                trace_event_data->phase,
                trace_event_data->process_id,
                (unsigned long long)trace_event_data->thread_id,
                (unsigned long long)trace_event_data->timestamp,
                trace_event_data->value_name[0],
                trace_event_data->value[0],
                trace_event_data->value_name[1],
                trace_event_data->value[1]);
            break;
        case STRING_ARG_1:
            fprintf(
                s_trace->fp,
                "{\"cat\":\"%s\",\"name\":\"%s\",\"ph\":\"%c\",\"pid\":%i,\"tid\":%llu,\"ts\":%llu,\"args\":{\"%s\":\"%"
                "s\"}},\n",
                trace_event_data->category,
                trace_event_data->name,
                trace_event_data->phase,
                trace_event_data->process_id,
                (unsigned long long)trace_event_data->thread_id,
                (unsigned long long)trace_event_data->timestamp,
                trace_event_data->value_name[0],
                trace_event_data->value_str[0]);
            break;
        case STRING_ARG_2:
            fprintf(
                s_trace->fp,
                "{\"cat\":\"%s\",\"name\":\"%s\",\"ph\":\"%c\",\"pid\":%i,\"tid\":%llu,\"ts\":%llu,\"args\":{\"%s\":\"%"
                "s\",\"%s\":\"%s\"}},\n",
                trace_event_data->category,
                trace_event_data->name,
                trace_event_data->phase,
                trace_event_data->process_id,
                (unsigned long long)trace_event_data->thread_id,
                (unsigned long long)trace_event_data->timestamp,
                trace_event_data->value_name[0],
                trace_event_data->value_str[0],
                trace_event_data->value_name[1],
                trace_event_data->value_str[1]);
            break;
        /* write nothing if incorrect num_args is given */
        default:
            return;
    }
}

static void s_trace_event_system_clean_up(void) {
    if (!s_trace) {
        return;
    }
    /* if bus was not initiated clean up trace_system only */
    if (!s_trace->bus.impl) {
        goto release_trace_event;
    }

    aws_bus_unsubscribe(&(s_trace->bus), 0, s_trace_event_write, NULL);
    aws_bus_clean_up(&(s_trace->bus));

    if (s_trace->fp != NULL) {
        /* Add number of events recorded */
        fprintf(
            s_trace->fp,
            "{\"cat\":\"TraceData\", "
            "\"name\":\"NumTraceEvent\",\"ph\":\"C\",\"pid\":%i,\"tid\":%i,\"ts\":%i,\"args\":{\"NumberOfTraces\":%i}}]"
            "\n",
            0,
            0,
            0,
            s_trace->num_traces);
        /* Set time display units */
        if (s_trace->time_unit == AWS_TRACE_SYSTEM_DISPLAY_NANO) {
            fprintf(s_trace->fp, ",\"displayTimeUnit\": \"ns\"");
        }
        fprintf(s_trace->fp, "}\n");

        fclose(s_trace->fp);
    }

release_trace_event:
    aws_mem_release(s_trace->allocator, s_trace);
}

/*
 * Public API
 */

void aws_trace_system_clean_up(void) {
    s_trace_event_system_clean_up();
}

/* starts the message bus and trace system */
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
    /* TODO: Add option to select sync vs async */
    struct aws_bus_options options = {
        .allocator = s_trace->allocator,
        .policy = AWS_BUS_SYNC,
    };
    if (aws_bus_init(&(s_trace->bus), &options)) {
        goto error;
    }
    if (aws_bus_subscribe(&(s_trace->bus), 0, s_trace_event_write, NULL)) {
        goto error;
    }

    /* Set starting time for program */
    if (aws_high_res_clock_get_ticks(&(s_trace->start_time))) {
        goto error;
    }

    /* Open filename.json to write data out */
    if (filename != NULL) {
        s_trace->fp = fopen(filename, "w");
        if (s_trace->fp) {
            fprintf(s_trace->fp, "{\"traceEvents\":[\n");
        }
    }

    return AWS_OP_SUCCESS;
error:
    aws_trace_system_clean_up();
    return AWS_OP_ERR;
}

void aws_trace_event(
    const char *category,
    const char *name,
    char phase,
    int value_1,
    const char *value_name_1,
    int value_2,
    const char *value_name_2) {

    /* Do nothing if trace system is not initialized */
    if (!s_trace) {
        return;
    }

    /* set timestamps are in nanoseconds */
    uint64_t timestamp;

    AWS_FATAL_ASSERT(!aws_high_res_clock_get_ticks(&timestamp));

    timestamp -= s_trace->start_time;

    /* convert timestamps to tracing format of microseconds */
    timestamp = aws_timestamp_convert(timestamp, AWS_TIMESTAMP_NANOS, AWS_TIMESTAMP_MICROS, 0);

    /* get calling thread and process ids */
    uint64_t thread_id = (uint64_t)aws_thread_current_thread_id();
    int process_id = aws_get_pid();

    struct aws_trace_event_data trace_event_data = {
        .phase = phase,
        .timestamp = timestamp,
        .thread_id = thread_id,
        .process_id = process_id,
    };

    trace_event_data.name = name;
    trace_event_data.category = category;

    if (phase == EVENT_PHASE_COUNTER) {
        trace_event_data.id = thread_id;
    }
    trace_event_data.args = NO_ARG;
    /* addding args data to trace event */
    if (value_name_1 != NULL) {
        trace_event_data.args = INT_ARG_1;
        trace_event_data.value[0] = value_1;
        trace_event_data.value_name[0] = value_name_1;

        if (value_name_2 != NULL) {
            trace_event_data.args = INT_ARG_2;
            trace_event_data.value[1] = value_2;
            trace_event_data.value_name[1] = value_name_2;
        }
    }

    /* send to the bus */
    AWS_FATAL_ASSERT(!aws_bus_send(&(s_trace->bus), 0, &trace_event_data, NULL));
}

void aws_trace_event_str(
    const char *category,
    const char *name,
    char phase,
    const char *value_1,
    const char *value_name_1,
    const char *value_2,
    const char *value_name_2) {

    /* Do nothing if trace system is not initialized */
    if (!s_trace) {
        return;
    }
    /* set timestamps are in nanoseconds */
    uint64_t timestamp;

    AWS_FATAL_ASSERT(!aws_high_res_clock_get_ticks(&timestamp));
    timestamp -= s_trace->start_time;
    /* convert timestamps to tracing format of microseconds */
    timestamp = aws_timestamp_convert(timestamp, AWS_TIMESTAMP_NANOS, AWS_TIMESTAMP_MICROS, 0);

    uint64_t thread_id = (uint64_t)aws_thread_current_thread_id();
    int process_id = aws_get_pid();

    struct aws_trace_event_data trace_event_data = {
        .phase = phase,
        .timestamp = 0,
        .thread_id = thread_id,
        .process_id = process_id,
    };

    trace_event_data.name = name;
    trace_event_data.category = category;
    trace_event_data.args = NO_ARG;

    /* Only add non NULL strings to the trace event data */
    if (value_1 != NULL) {
        trace_event_data.value_str[0] = value_1;
    }

    if (value_name_1 != NULL) {
        trace_event_data.value_name[0] = value_name_1;
        trace_event_data.args = STRING_ARG_1;
    }

    if (value_2 != NULL) {
        trace_event_data.value_str[1] = value_2;
    }

    if (value_name_2 != NULL) {
        trace_event_data.value_name[1] = value_name_2;
        trace_event_data.args = STRING_ARG_2;
    }

    /* send to the bus */
    AWS_FATAL_ASSERT(!aws_bus_send(&(s_trace->bus), 0, &trace_event_data, NULL));
}
