#ifndef AWS_COMMON_TRACE_EVENT_H
#define AWS_COMMON_TRACE_EVENT_H
/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

/* Disable warnings with windows build */
#ifdef _MSC_VER
#    pragma warning(disable : C4996)
#endif

#include <aws/common/clock.h>
#include <aws/common/common.h>

AWS_EXTERN_C_BEGIN

#define AWS_TRACE_EVENT_BEGIN(category, name) aws_trace_event_new(category, name, EVENT_PHASE_BEGIN)

#define AWS_TRACE_EVENT_END(category, name) aws_trace_event_new(category, name, EVENT_PHASE_END)

#define AWS_TRACE_EVENT_INSTANT(category, name) aws_trace_event_new(category, name, EVENT_PHASE_INSTANT)
// Phase macros
//! add more phase types later as the app progresses
#define EVENT_PHASE_BEGIN ('B')
#define EVENT_PHASE_END ('E')
#define EVENT_PHASE_INSTANT ('I')

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
    /* args for more metadata to be added later */
};

/*
 * MUST CALL TO START TRACE SYSTEM
 * Starts the aws_message_bus in a background thread and subscribes the listener to it.
 * Initializes a JSON object to store trace event data
 * Must be called before using event_trace_add or close_event_trace
 * time_unit is the time measurement used. See clock.h for options
 */
AWS_COMMON_API
int aws_trace_system_init(enum aws_timestamp_unit time_unit, struct aws_allocator *allocator);

/*
 * MUST CALL TO AVOID MEMORY LEAKS
 * Cleans up the aws_message_bus and unsubscribes the listener.
 * Prints the JSON object that stores trace event data to the given filename
 * as a .JSON file.
 * Closes the JSON object and frees all allocated memory.
 * Code 0 to not write out file and Code 1 to write out to file
 */
AWS_COMMON_API
void aws_trace_system_clean_up(int code, const char *filename);

/*
 * Sends event trace data to the aws_message_bus to be added to
 * a JSON object. Use strdup("***") for category and name when using c++
 * phase can be B/E for event starts and stops added in the same scope and
 * S/F for events in different scopes
 */
AWS_COMMON_API
int aws_trace_event_new(const char *category, const char *name, char phase);

/*
 * Used for debugging
 */
AWS_COMMON_API
void *aws_trace_event_get_root(void);

AWS_EXTERN_C_END
#endif /* AWS_COMMON_TRACE_EVENT_H */
