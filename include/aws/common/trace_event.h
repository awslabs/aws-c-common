#ifndef AWS_COMMON_TRACE_EVENT_H
#define AWS_COMMON_TRACE_EVENT_H
/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/common/common.h>

AWS_EXTERN_C_BEGIN

#define AWS_TRACE_EVENT_BEGIN(category, name) aws_trace_event(category, name, EVENT_PHASE_BEGIN, 0, NULL)

#define AWS_TRACE_EVENT_END(category, name) aws_trace_event(category, name, EVENT_PHASE_END, 0, NULL)

#define AWS_TRACE_EVENT_INSTANT(category, name) aws_trace_event(category, name, EVENT_PHASE_INSTANT, 0, NULL)

#define AWS_TRACE_EVENT_COUNTER(category, name, value)                                                                 \
    aws_trace_event(category, name, EVENT_PHASE_COUNTER, value, #value)

// Phase macros
//! add more phase types later as the app progresses
#define EVENT_PHASE_BEGIN ('B')
#define EVENT_PHASE_END ('E')
#define EVENT_PHASE_INSTANT ('I')
#define EVENT_PHASE_COUNTER ('C')

#define AWS_TRACE_EVENT_TIME_DISPLAY_MICRO 0
#define AWS_TRACE_EVENT_TIME_DISPLAY_NANO 1

/*
 * MUST CALL TO AVOID MEMORY LEAKS
 * Cleans up the aws_message_bus and unsubscribes the listener.
 * Closes the JSON object and frees all allocated memory.
 */
AWS_COMMON_API
void aws_trace_system_clean_up(void);

/*
 * MUST CALL TO START TRACE SYSTEM
 * Starts the aws_message_bus in a background thread and subscribes the listener to it.
 * Initializes a JSON object to store trace event data
 * Must be called before using event_trace_add or close_event_trace
 * Put NULL for filename to not write out to json file
 * Filename must be a string literal to write out to json file
 */
AWS_COMMON_API
int aws_trace_system_init(const char *filename, struct aws_allocator *allocator);

/*
 * Sends event trace data to the aws_message_bus to be added to
 * a JSON object.
 * Category and name and value name must be string literals
 * phase can be B/E for event starts and stops added in the same scope and
 * S/F for events in different scopes
 */
AWS_COMMON_API
int aws_trace_event(const char *category, const char *name, char phase, int value, const char *value_name);

/*
 *
 */
// AWS_COMMON_API
// int aws_trace_event_new_counter(const char *category, const char *name, int value, const char* value_name);

/*
 * Used for debugging
 */
AWS_COMMON_API
void *aws_trace_event_get_root(void);

AWS_EXTERN_C_END
#endif /* AWS_COMMON_TRACE_EVENT_H */
