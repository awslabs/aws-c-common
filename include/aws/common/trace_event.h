#ifndef AWS_COMMON_TRACE_EVENT_H
#define AWS_COMMON_TRACE_EVENT_H
/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/common/common.h>
#include <limits.h>

AWS_EXTERN_C_BEGIN

/* INTERNAL USAGE MACROS, DO NOT CALL THESE OUTSIDE OF THIS HEADER FILE */
/* AWS_TRACE_EVENT MACRO OVERLOADS */
#define AWS_TRACE_EVENT5(phase, category, name, value1, value2)                                                        \
    do {                                                                                                               \
        if ((value1) == INT_MIN) {                                                                                     \
            aws_trace_event(category, name, phase, 0, NULL, 0, NULL);                                                  \
        } else if ((value2) == INT_MIN) {                                                                              \
            aws_trace_event(category, name, phase, value1, #value1, 0, NULL);                                          \
        } else {                                                                                                       \
            aws_trace_event(category, name, phase, value1, #value1, value2, #value2);                                  \
        }                                                                                                              \
    } while (0)
#define AWS_TRACE_EVENT4(category, name, phase, value1) AWS_TRACE_EVENT5(category, name, phase, value1, INT_MIN)
#define AWS_TRACE_EVENT3(phase, category, name) AWS_TRACE_EVENT4(phase, category, name, INT_MIN)
#define AWS_TRACE_EVENT2(phase, category) AWS_TRACE_EVENT3(phase, category, NULL)
#define AWS_TRACE_EVENT1(phase) AWS_TRACE_EVENT2(category, NULL)

/* AWS_TRACE_EVENT_STR MACRO OVERLOADS */
#define AWS_TRACE_EVENT_STR5(phase, category, name, value1, value2)                                                    \
    do {                                                                                                               \
        if ((value1) == NULL) {                                                                                        \
            aws_trace_event_str(category, name, phase, NULL, NULL, NULL, NULL);                                        \
        } else if ((value2) == NULL) {                                                                                 \
            aws_trace_event_str(category, name, phase, value1, #value1, NULL, NULL);                                   \
        } else {                                                                                                       \
            aws_trace_event_str(category, name, phase, value1, #value1, value2, #value2);                              \
        }                                                                                                              \
    } while (0)
#define AWS_TRACE_EVENT_STR4(phase, category, name, value1) AWS_TRACE_EVENT_STR5(phase, category, name, value1, NULL)
#define AWS_TRACE_EVENT_STR3(phase, category, name) AWS_TRACE_EVENT_STR4(phase, category, name, NULL)
#define AWS_TRACE_EVENT_STR2(phase, category) AWS_TRACE_EVENT_STR3(phase, category, NULL)
#define AWS_TRACE_EVENT_STR1(phase) AWS_TRACE_EVENT_STR2(phase, NULL)

#define AWS_TRACE_EVENT_OVERLOAD(phase, ...) CALL_OVERLOAD(AWS_TRACE_EVENT, phase, __VA_ARGS__)
#define AWS_TRACE_EVENT_STR_OVERLOAD(phase, ...) CALL_OVERLOAD(AWS_TRACE_EVENT_STR, phase, __VA_ARGS__)

/* PUBLIC USAGE MACROS */

/* ALL TRACE_EVENT MACROS REQUIRE CATEGORY AND NAME AS STRING LITERAL ARGUMENTS  */
/* ALL TRACE_EVENT MACROS THAT ARE NOT SUFFIXED WITH _STR ACCEPT UP TO 2 INTEGER ARGUMENTS AFTER CATEGORY AND NAME */
/* ALL TRACE_EVENT MACROS THAT ARE SUFFIXED WITH _STR ACCEPT UP TO 2 STRING LITERAL ARGUMENTS AFTER CATEGORY AND NAME */
/* NAME_THREAD, NAME_PROCESS, AND _SCOPED ARE EXCLUDED FROM THESE RULES */

/* DURATION EVENTS */
/* Scoped Duration Events */
/* Creates local variable for END_SCOPE for easier markups of duration events */
/* Only one BEGIN can exist per function scope, with multiple END's for each exit point in the scope */
#define AWS_TRACE_EVENT_BEGIN_SCOPED(category, name)                                                                   \
    const char *scoped_category = category;                                                                            \
    const char *scoped_name = name;                                                                                    \
    aws_trace_event(scoped_category, scoped_name, EVENT_PHASE_BEGIN, 0, NULL, 0, NULL)
#define AWS_TRACE_EVENT_END_SCOPED() aws_trace_event(scoped_category, scoped_name, EVENT_PHASE_END, 0, NULL, 0, NULL)

/* Marks start of a duration event */
/* Parameter Order: category, name, optional_arg1, optional_arg2 */
#define AWS_TRACE_EVENT_BEGIN(...) AWS_TRACE_EVENT_OVERLOAD(EVENT_PHASE_BEGIN, __VA_ARGS__)
#define AWS_TRACE_EVENT_BEGIN_STR(...) AWS_TRACE_EVENT_STR_OVERLOAD(EVENT_PHASE_BEGIN, __VA_ARGS__)

/* Marks the end of a duration event */
/* Parameter Order: category, name, optional_arg1, optional_arg2 */
#define AWS_TRACE_EVENT_END(...) AWS_TRACE_EVENT_OVERLOAD(EVENT_PHASE_END, __VA_ARGS__)
#define AWS_TRACE_EVENT_END_STR(...) AWS_TRACE_EVENT_STR_OVERLOAD(EVENT_PHASE_END, __VA_ARGS__)

/* INSTANT EVENTS */
/* Marks an instant event */
/* Records a snapshot of data at that point */
/* Parameter Order: category, name, optional_arg1, optional_arg2 */
#define AWS_TRACE_EVENT_INSTANT(...) AWS_TRACE_EVENT_OVERLOAD(EVENT_PHASE_INSTANT, __VA_ARGS__)
#define AWS_TRACE_EVENT_INSTANT_STR(...) AWS_TRACE_EVENT_STR_OVERLOAD(EVENT_PHASE_INSTANT, __VA_ARGS__)

/* COUNTER EVENTS */
/* Marks a variable for a counter event */
/* Records the variable's value throughout the duration of the program */
/* Requires at least 1 integer argument can have up to 2 */
/* Parameter Order: category, name, arg1, optional_arg2 */
#define AWS_TRACE_EVENT_COUNTER(...) AWS_TRACE_EVENT_OVERLOAD(EVENT_PHASE_COUNTER, __VA_ARGS__)

/* METADATA EVENTS */
/* Metadata event for naming threads/processes */
#define AWS_TRACE_EVENT_NAME_THREAD(thread_name)                                                                       \
    aws_trace_event_str("__metadata", "thread_name", EVENT_PHASE_METADATA, thread_name, "name", NULL, NULL)
#define AWS_TRACE_EVENT_NAME_PROCESS(process_name)                                                                     \
    aws_trace_event_str("__metadata", "process_name", EVENT_PHASE_METADATA, process_name, "name", NULL, NULL)

/* Phase macros */
#define EVENT_PHASE_NULL ('.')
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
/* Options for trace system, used at intialization */

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
 * Call at the end of your program's lifetime
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
