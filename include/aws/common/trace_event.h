#ifndef AWS_COMMON_TRACE_EVENT_H
#define AWS_COMMON_TRACE_EVENT_H
/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/common/common.h>

AWS_EXTERN_C_BEGIN
/* duration events */
#define AWS_TRACE_EVENT_BEGIN(category, name) aws_trace_event(category, name, EVENT_PHASE_BEGIN, 0, NULL, 0, NULL)
#define AWS_TRACE_EVENT_END(category, name) aws_trace_event(category, name, EVENT_PHASE_END, 0, NULL, 0, NULL)
/* duration events with args */
/* Duplicate args in matching duration events will be overwritten by args in ENDx */
#define AWS_TRACE_EVENT_BEGIN1(category, name, value)                                                                  \
    aws_trace_event(category, name, EVENT_PHASE_BEGIN, value, #value, 0, NULL)
#define AWS_TRACE_EVENT_BEGIN2(category, name, value1, value2)                                                         \
    aws_trace_event(category, name, EVENT_PHASE_BEGIN, value1, #value1, value2, #value2)
#define AWS_TRACE_EVENT_END1(category, name, value)                                                                    \
    aws_trace_event(category, name, EVENT_PHASE_END, value, #value, 0, NULL)
#define AWS_TRACE_EVENT_END2(category, name, value1, value2)                                                           \
    aws_trace_event(category, name, EVENT_PHASE_END, value1, #value1, value2, #value2)

/* instant events */
#define AWS_TRACE_EVENT_INSTANT(category, name) aws_trace_event(category, name, EVENT_PHASE_INSTANT, 0, NULL, 0, NULL)
/* instant events with args */
#define AWS_TRACE_EVENT_INSTANT1(category, name, value)                                                                \
    aws_trace_event(category, name, EVENT_PHASE_INSTANT, value, #value, 0, NULL)
#define AWS_TRACE_EVENT_INSTANT2(category, name, value1, value2)                                                       \
    aws_trace_event(category, name, EVENT_PHASE_INSTANT, value1, #value1, value2, #value2)

/* counter events */
#define AWS_TRACE_EVENT_COUNTER1(category, name, value)                                                                \
    aws_trace_event(category, name, EVENT_PHASE_COUNTER, value, #value, 0, NULL)
#define AWS_TRACE_EVENT_COUNTER2(category, name, value1, value2)                                                       \
    aws_trace_event(category, name, EVENT_PHASE_COUNTER, value1, #value1, value2, #value2)

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
int aws_trace_system_init(struct aws_allocator *allocator, const char *filename);

/*
 * Sends event trace data to the aws_message_bus to be added to
 * a JSON object.
 * Category and name and value name must be string literals
 * phase can be B/E for duration, I for instant, and C for counter events
 */
AWS_COMMON_API
void aws_trace_event(
    const char *category,
    const char *name,
    char phase,
    int value_1,
    const char *value_name_1,
    int value_2,
    const char *value_name_2);

AWS_EXTERN_C_END
#endif /* AWS_COMMON_TRACE_EVENT_H */


//notes
//allow init to gracefulkly clean up and have functions not do anything if init does not work
