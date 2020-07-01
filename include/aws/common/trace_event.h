#ifndef AWS_COMMON_TRACE_EVENT_H
#define AWS_COMMON_TRACE_EVENT_H
/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/common/bus.h>
#include <aws/common/cJSON.h>
#include <aws/common/common.h>
#include <aws/common/thread.h>
#include <aws/common/process.h>
AWS_EXTERN_C_BEGIN

/* Must use INIT before calling any other macros*/
#define AWS_TRACE_EVENT_INIT(address) aws_trace_event_init(address, aws_default_allocator())
#define AWS_TRACE_EVENT_INIT_(address, allocator) aws_trace_event_init(address, allocator)

/* For use in cpp programs */
#define AWS_TRACE_EVENT_BEGIN_CPP(category, name) aws_trace_event_new(strdup(category), strdup(name), EVENT_PHASE_BEGIN)
#define AWS_TRACE_EVENT_END_CPP(category, name) aws_trace_event_new(strdup(category), strdup(name), EVENT_PHASE_END)

/* For use in c programs */
#define AWS_TRACE_EVENT_BEGIN(category, name) aws_trace_event_new(category, name, EVENT_PHASE_BEGIN)
#define AWS_TRACE_EVENT_END(category, name) aws_trace_event_new(category, name, EVENT_PHASE_END)

/* To clean up and to write trace event metadata to JSON file */
#define AWS_TRACE_EVENT_CLEAN_UP_OUT(output_file) aws_trace_event_clean_up(1, output_file)
#define AWS_TRACE_EVENT_CLEAN_UP_OUT_CPP(output_file) aws_trace_event_clean_up(1, strdup(output_file))

/* To clean up without writing to JSON file */
#define AWS_TRACE_EVENT_CLEAN_UP() aws_trace_event_clean_up(0, NULL)
#define AWS_TRACE_EVENT_CLEAN_UP() aws_trace_event_clean_up(0, NULL)

// Phase macros
//! add more phase types later as the app progresses
#define EVENT_PHASE_BEGIN ('B')
#define EVENT_PHASE_END ('E')

struct aws_trace_event_metadata {
    /* should be B/E for same scope or S/F for outside of scope */
    char phase;
    /* name of the event */
    char *name;
    /* category of the event */
    char *category;
    /* timestamp in milliseconds */
    unsigned long long timestamp;
    unsigned long int thread_id;
    int process_id;
    /* args for more metadata to be added later */
};

struct aws_trace_event {
    struct cJSON *root, *event_array;
    struct aws_bus bus;
    struct aws_allocator *allocator;
};

//! this function can go solely in the .c file
/*
 * Subscirbes to the aws_message_bus and writes trace event data
 * to a JSON object when it is thread safe to do so.
 */
// AWS_COMMON_API
// void aws_trace_event_listener(uint64_t address, const void *msg, void *user_data);

/*
 * Starts the aws_message_bus in a background thread and subscribes the listener to it.
 * Initializes a JSON object to store trace event data
 * Must be called before using event_trace_add or close_event_trace
 * Listener_id is the assigned id integer of the listener function
 */
AWS_COMMON_API
int aws_trace_event_init(uint64_t address, struct aws_allocator *allocator);

/*
 * Cleans up the aws_message_bus and unsubscribes the listener.
 * Prints the JSON object that stores trace event data to the given filename
 * as a .JSON file.
 * Closes the JSON object and frees all allocated memory.
 */
AWS_COMMON_API
int aws_trace_event_clean_up(int code, char *filename);

//! this function can go solely in the .c file
// free trace event memory
// AWS_COMMON_API
// void aws_trace_event_destroy(void *payload);

/*
 * Sends event trace data to the aws_message_bus to be added to
 * a JSON object. Use strdup("***") for category and name when using c++
 * phase can be B/E for event starts and stops added in the same scope and
 * S/F for events in different scopes
 */
AWS_COMMON_API
int aws_trace_event_new(char *category, char *name, char phase);

/*
 * Used for debugging
 *
 * AWS_COMMON_API
 */
struct cJSON *aws_trace_event_get_root(void);

AWS_EXTERN_C_END
#endif /* AWS_COMMON_TRACE_EVENT_H */
