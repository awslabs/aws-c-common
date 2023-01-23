/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */
#include <aws/common/bus.h>
#include <aws/common/clock.h>
#include <aws/common/file.h>
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
    struct aws_bus *bus;
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
    struct aws_allocator *allocator;
    /* should be B/E for duration, I for instant, C for counter, and M for metadata */
    char phase;
    /* name of the event */
    const char *name;
    /* category of the event */
    const char *category;
    /* timestamp in milliseconds */
    uint64_t timestamp;
    /* calling thread/process id */
    uint64_t thread_id;
    int process_id;
    /* used to id the event */
    int id;
    /* keeps track of arg type and number */
    enum trace_event_args args;
    /* stores optional args and optional args' name */
    int value[2];
    const char *value_name[2];
    char value_str[2][16];
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

static void s_trace_event_system_clean_up(struct trace_system *trace) {
    if (!trace) {
        return;
    }

    /* if bus was not initiated clean up trace_system only */
    if (!trace->bus) {
        goto release_trace_event;
    }

    aws_bus_unsubscribe(trace->bus, (uint64_t)trace, s_trace_event_write, NULL);
    aws_bus_destroy(trace->bus);

    if (trace->fp != NULL) {
        /* Add number of events recorded */
        fprintf(
            trace->fp,
            "{\"cat\":\"TraceData\", "
            "\"name\":\"NumTraceEvent\",\"ph\":\"C\",\"pid\":%i,\"tid\":%i,\"ts\":%i,\"args\":{\"NumberOfTraces\":%i}},"
            "\n",
            0,
            0,
            0,
            trace->num_traces);
        fprintf(
            trace->fp,
            "{\"cat\":\"__metadata\", "
            "\"name\":\"thread_name\",\"ph\":\"M\",\"pid\":%i,\"tid\":%i,\"ts\":%i,\"args\":{\"name\":\"Trace "
            "Counter\"}}]"
            "\n",
            0,
            0,
            0);
        /* Set time display units */
        if (trace->time_unit == AWS_TRACE_SYSTEM_DISPLAY_NANO) {
            fprintf(trace->fp, ",\"displayTimeUnit\": \"ns\"");
        }
        fprintf(trace->fp, "}\n");

        fclose(trace->fp);
    }

release_trace_event:
    aws_mem_release(trace->allocator, trace);
}

/*
 * Public API
 */

void aws_trace_system_clean_up(void) {
    struct trace_system *trace = s_trace;
    s_trace = NULL;
    s_trace_event_system_clean_up(trace);
}

/* starts the message bus and trace system */
int aws_trace_system_init(struct aws_allocator *allocator, const char *filename) {
    if (allocator == NULL) {
        aws_raise_error(AWS_ERROR_INVALID_ARGUMENT);
        return AWS_OP_ERR;
    }

    struct trace_system *trace = aws_mem_calloc(allocator, 1, sizeof(struct trace_system));

    trace->allocator = allocator;
    /* start the message bus */
    /* TODO: Add option to select sync vs async */
    struct aws_bus_options options = {
        .policy = AWS_BUS_ASYNC_RELIABLE,
    };
    trace->bus = aws_bus_new(allocator, &options);
    if (!trace->bus) {
        goto error;
    }
    if (aws_bus_subscribe(trace->bus, (uint64_t)trace, s_trace_event_write, NULL)) {
        goto error;
    }

    /* Set starting time for program */
    if (aws_high_res_clock_get_ticks(&(trace->start_time))) {
        goto error;
    }
    /* time unit is initially set to micro unless changed in options */
    trace->time_unit = AWS_TRACE_SYSTEM_DISPLAY_MICRO;

    /* Open filename.json to write data out */
    if (filename != NULL) {
        trace->fp = aws_fopen(filename, "w");
        if (trace->fp) {
            fprintf(trace->fp, "{\"traceEvents\":[\n");
        }
    }

    s_trace = trace;
    return AWS_OP_SUCCESS;
error:
    s_trace_event_system_clean_up(trace);
    return AWS_OP_ERR;
}

static void s_trace_event_data_destroy(void *user_data) {
    struct aws_trace_event_data *event = user_data;
    aws_mem_release(event->allocator, event);
}

static void s_trace_event(
    const char *category,
    const char *name,
    char phase,
    const char *value_name_a,
    const char *value_str_a,
    int value_int_a,
    const char *value_name_b,
    const char *value_str_b,
    int value_int_b) {

    /* Do nothing if trace system is not initialized */
    if (!s_trace) {
        return;
    }

    /* set timestamps are in nanoseconds */
    uint64_t timestamp;

    AWS_FATAL_ASSERT(!aws_high_res_clock_get_ticks(&timestamp));

    timestamp -= s_trace->start_time;

    /* convert timestamps to tracing format of microseconds */
    if (s_trace->time_unit == AWS_TRACE_SYSTEM_DISPLAY_MICRO) {
        timestamp = aws_timestamp_convert(timestamp, AWS_TIMESTAMP_NANOS, AWS_TIMESTAMP_MICROS, 0);
    }

    /* get calling thread and process ids */
    uint64_t thread_id = (uint64_t)aws_thread_current_thread_id();
    int process_id = aws_get_pid();

    struct aws_trace_event_data *trace_event_data =
        aws_mem_calloc(s_trace->allocator, 1, sizeof(struct aws_trace_event_data));

    trace_event_data->allocator = s_trace->allocator;
    trace_event_data->phase = phase;
    trace_event_data->timestamp = timestamp;
    trace_event_data->thread_id = thread_id;
    trace_event_data->process_id = process_id;
    trace_event_data->name = name;
    trace_event_data->category = category;

    if (phase == EVENT_PHASE_COUNTER) {
        trace_event_data->id = thread_id;
    }

    trace_event_data->args = NO_ARG;
    if (value_name_a) {
        trace_event_data->value_name[0] = value_name_a;
        if (value_str_a) {
            trace_event_data->args = STRING_ARG_1;
            strncpy(trace_event_data->value_str[0], value_str_a, sizeof(trace_event_data->value_str[0]) - 1);
        } else {
            trace_event_data->args = INT_ARG_1;
            trace_event_data->value[0] = value_int_a;
        }
    }
    if (value_name_b) {
        trace_event_data->value_name[1] = value_name_b;
        if (value_str_b) {
            trace_event_data->args = STRING_ARG_2;
            strncpy(trace_event_data->value_str[1], value_str_b, sizeof(trace_event_data->value_str[1]) - 1);
        } else {
            trace_event_data->args = INT_ARG_2;
            trace_event_data->value[1] = value_int_b;
        }
    }

    /* send to the bus */
    AWS_FATAL_ASSERT(!aws_bus_send(s_trace->bus, (uint64_t)s_trace, trace_event_data, s_trace_event_data_destroy));
}

void aws_trace_event(
    const char *category,
    const char *name,
    char phase,
    int value_1,
    const char *value_name_1,
    int value_2,
    const char *value_name_2) {

    s_trace_event(
        category,
        name,
        phase,
        value_name_1,
        NULL /*value_str_1*/,
        value_1,
        value_name_2,
        NULL /*value_str_2*/,
        value_2);
}

void aws_trace_event_str(
    const char *category,
    const char *name,
    char phase,
    const char *value_1,
    const char *value_name_1,
    const char *value_2,
    const char *value_name_2) {

    s_trace_event(
        category, name, phase, value_name_1, value_1, 0 /*value_int_1*/, value_name_2, value_2, 0 /*value_int_2*/);
}
