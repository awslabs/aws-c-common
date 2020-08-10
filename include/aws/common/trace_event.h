#ifndef AWS_COMMON_TRACE_EVENT_H
#define AWS_COMMON_TRACE_EVENT_H
/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/common/common.h>

AWS_EXTERN_C_BEGIN
/* Markup Macros to call aws_trace_event and aws_trace_event_str for different event types and argument types */

/* duration events */
#define AWS_TRACE_EVENT_BEGIN(category, name) aws_trace_event(category, name, EVENT_PHASE_BEGIN, 0, NULL, 0, NULL)
#define AWS_TRACE_EVENT_END(category, name) aws_trace_event(category, name, EVENT_PHASE_END, 0, NULL, 0, NULL)
/* duration events with integer args */
/* Duplicate args in matching duration events will be overwritten by args in ENDx */
#define AWS_TRACE_EVENT_BEGIN1(category, name, value)                                                                  \
    aws_trace_event(category, name, EVENT_PHASE_BEGIN, value, #value, 0, NULL)
#define AWS_TRACE_EVENT_BEGIN2(category, name, value1, value2)                                                         \
    aws_trace_event(category, name, EVENT_PHASE_BEGIN, value1, #value1, value2, #value2)
#define AWS_TRACE_EVENT_END1(category, name, value)                                                                    \
    aws_trace_event(category, name, EVENT_PHASE_END, value, #value, 0, NULL)
#define AWS_TRACE_EVENT_END2(category, name, value1, value2)                                                           \
    aws_trace_event(category, name, EVENT_PHASE_END, value1, #value1, value2, #value2)

/* duration events with string literal arguments */
#define AWS_TRACE_EVENT_BEGIN_STR1(category, name, string)                                                             \
    aws_trace_event_str(category, name, EVENT_PHASE_BEGIN, string, #string, NULL, NULL)
#define AWS_TRACE_EVENT_BEGIN_STR2(category, name, string_1, string_2)                                                 \
    aws_trace_event_str(category, name, EVENT_PHASE_BEGIN, string_1, #string_1, string_2, #string_2)
#define AWS_TRACE_EVENT_END_STR1(category, name, string)                                                               \
    aws_trace_event_str(category, name, EVENT_PHASE_END, string, #string, NULL, NULL)
#define AWS_TRACE_EVENT_END_STR2(category, name, string_1, string_2)                                                   \
    aws_trace_event_str(category, name, EVENT_PHASE_END, string_1, #string_1, string_2, #string_2)

/* instant events */
#define AWS_TRACE_EVENT_INSTANT(category, name) aws_trace_event(category, name, EVENT_PHASE_INSTANT, 0, NULL, 0, NULL)

/* instant events with args to track integers or string literals */
#define AWS_TRACE_EVENT_INSTANT1(category, name, value)                                                                \
    aws_trace_event(category, name, EVENT_PHASE_INSTANT, value, #value, 0, NULL)
#define AWS_TRACE_EVENT_INSTANT2(category, name, value1, value2)                                                       \
    aws_trace_event(category, name, EVENT_PHASE_INSTANT, value1, #value1, value2, #value2)
#define AWS_TRACE_EVENT_INSTANT_STR1(category, name, string)                                                           \
    aws_trace_event_str(category, name, EVENT_PHASE_INSTANT, string, #string, NULL, NULL)
#define AWS_TRACE_EVENT_INSTANT_STR2(category, name, string_1, string_2)                                               \
    aws_trace_event_str(category, name, EVENT_PHASE_INSTANT, string_1, #string_1, string_2, #string_2)

/* counter events */
/* Counter events are process local */
/* Counter events can take 1 to 2 integer values to track */
#define AWS_TRACE_EVENT_COUNTER1(category, name, value)                                                                \
    aws_trace_event(category, name, EVENT_PHASE_COUNTER, value, #value, 0, NULL)
#define AWS_TRACE_EVENT_COUNTER2(category, name, value1, value2)                                                       \
    aws_trace_event(category, name, EVENT_PHASE_COUNTER, value1, #value1, value2, #value2)

/* Metadata event for naming threads/processes */
/* Category and name can be arbitrary */
#define AWS_TRACE_EVENT_NAME_THREAD(thread_name)                                                                       \
    aws_trace_event_str("__metadata", "thread_name", EVENT_PHASE_METADATA, thread_name, "name", NULL, NULL)
#define AWS_TRACE_EVENT_NAME_PROCESS(category, name, process_name)                                                     \
    aws_trace_event_str("__metadata", "process_name", EVENT_PHASE_METADATA, process_name, "name", NULL, NULL)

/* Duration Event Macros */
/* Creates local variable for End scope for easier markups of duration events */
/* Only one pair of begin and end can exist per function scope */
#define AWS_TRACE_EVENT_BEGIN_SCOPE(category, name)                                                                    \
    const char *scoped_category = category;                                                                          \
    const char *scoped_name = name;                                                                                  \
    aws_trace_event(scoped_category, scoped_name, EVENT_PHASE_BEGIN, 0, NULL, 0, NULL)
#define AWS_TRACE_EVENT_END_SCOPE()                                                                                    \
    aws_trace_event(scoped_category, scoped_name, EVENT_PHASE_BEGIN, 0, NULL, 0, NULL)

/* Phase macros */
#define EVENT_PHASE_BEGIN ('B')
#define EVENT_PHASE_END ('E')
#define EVENT_PHASE_INSTANT ('I')
#define EVENT_PHASE_COUNTER ('C')
#define EVENT_PHASE_METADATA ('M')

/* Time Unit Display Setting for Chrome://tracing, default is microseconds */
enum aws_trace_system_time_display_unit {
    AWS_TRACE_SYSTEM_DISPLAY_MICRO,
    AWS_TRACE_SYSTEM_DISPLAY_NANO,
};

/*
struct trace_system_options{
        const char * filename;
        enum aws_bus_policy bus_policy;
        enum aws_trace_system_time_display_unit time_unit;
};
*/

/*
 * MUST CALL TO AVOID MEMORY LEAKS
 * Cleans up trace system
 * Cleans up the aws_message_bus and unsubscribes the listener.
 * Closes the JSON object and frees all allocated memory.
 */
AWS_COMMON_API
void aws_trace_system_clean_up(void);

/*
 * MUST CALL TO START TRACE SYSTEM
 * Starts the aws_message_bus in a background thread and subscribes the listener to it.
 * Open a json file to write trace events to
 * Must be called before using aws_trace_event, aws_trace_event_str, or aws_trace_system_clean_up
 * Put NULL for filename to not write out to json file
 * Filename must be a string literal to write out to json file
 * To turn off tracing, comment out this function wherever used.
 */
AWS_COMMON_API
int aws_trace_system_init(struct aws_allocator *allocator, const char *filename);

/*
 * Sends event trace data to the aws_message_bus to be written out to json file
 * Category and name and value name must be string literals
 * Value_1 and Value_2 can be provided for counter events or for args in duration and instant events
 * phase can be B/E for duration, I for instant, and C for counter events
 * Value_x must be an integer
 * Value_name_x will be string literals for Value_x's variable name
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

/*
 * Sends event trace data to the aws_message_bus to be written out to json file
 * Category and name and value name must be string literals
 * Value_1 and Value_2 can be provided for counter events or for args in duration and instant events
 * phase can be B/E for duration, I for instant, and C for counter events
 * Value_x must be a string literal
 * Value_name_x will be string literals for Value_x's variable name
 */
AWS_COMMON_API
void aws_trace_event_str(
    const char *category,
    const char *name,
    char phase,
    const char *value_1,
    const char *value_name_1,
    const char *value_2,
    const char *value_name_2);

AWS_EXTERN_C_END
#endif /* AWS_COMMON_TRACE_EVENT_H */
