#include <aws/common/bus.h>
#include <aws/common/cJSON.h>
#include <aws/common/clock.h>
#include <aws/common/common.h>
#include <aws/common/logging.h>
#include <aws/common/process.h>
#include <aws/common/trace_event.h>

struct aws_trace_event *trace_event;
uint64_t listener_id;
uint64_t start_time;

/*
 * Private API
 */

/* Add trace event meta data to JSON object when the message bus allows it */
void aws_trace_event_listener(uint64_t address, const void *msg, void *user_data) {
    struct aws_trace_event_metadata *trace_event_data = (struct aws_trace_event_metadata *)msg;
    cJSON *event = cJSON_CreateObject();

    cJSON_AddItemToArray(trace_event->event_array, event);
    /* add options for args later on, will initially be empty for now */
    cJSON_AddItemToObject(event, "args", cJSON_CreateObject());

    /* add more options later on */
    cJSON_AddStringToObject(event, "cat", trace_event_data->category);
    cJSON_AddStringToObject(event, "name", trace_event_data->name);
    cJSON_AddStringToObject(event, "ph", &(trace_event_data->phase));
    cJSON_AddNumberToObject(event, "pid", trace_event_data->process_id);
    cJSON_AddNumberToObject(event, "tid", trace_event_data->thread_id);
    cJSON_AddNumberToObject(event, "ts", trace_event_data->timestamp);
}

/* Destructor of trace event metadata sent through the bus */
void aws_trace_event_destroy(void *payload) {
    struct aws_trace_event_metadata *trace_event_data = (struct aws_trace_event_metadata *)payload;
    aws_mem_release(trace_event->allocator, trace_event_data->name);
    aws_mem_release(trace_event->allocator, trace_event_data->category);
}

/*
 * Public API
 */

/* starts the message bus and initializes the JSON root, and the event array for storing metadata */
int aws_trace_event_init(uint64_t address, struct aws_allocator *allocator) {
    trace_event = aws_mem_acquire(allocator, sizeof(struct aws_trace_event));
    trace_event->allocator = allocator;

    trace_event->root = cJSON_CreateObject();
    trace_event->event_array = cJSON_CreateArray();
    cJSON_AddItemToObject(trace_event->root, "traceEvents", trace_event->event_array);

    aws_high_res_clock_get_ticks(&start_time);
    listener_id = address;

    if (allocator == NULL || trace_event->root == NULL || trace_event->event_array == NULL) {
        return AWS_OP_ERR;
    }

    /* start the message bus */
    /* !!! POSSIBLY ADD OPTION TO CHOOSE SYNC VS ASYNC MAYBE? !!! */
    struct aws_bus_options options = {
        .allocator = allocator,
        .policy = AWS_BUS_SYNC,
    };
    aws_bus_init(&(trace_event->bus), &options);
    aws_bus_subscribe(&(trace_event->bus), listener_id, aws_trace_event_listener, NULL);

    return AWS_OP_SUCCESS;
}

int aws_trace_event_clean_up(int code, char *filename) {
    aws_bus_unsubscribe(&(trace_event->bus), listener_id, aws_trace_event_listener, NULL);
    aws_bus_clean_up(&(trace_event->bus));

    if (code && filename != NULL) {
        char *out = cJSON_Print((trace_event->root));
        FILE *fp;
        strcat(filename, ".json");

        fp = fopen(filename, "w");
        fprintf(fp, "%s", out);
        fclose(fp);
        aws_mem_release(trace_event->allocator, out);
    }
    cJSON_Delete(trace_event->root);
    aws_mem_release(trace_event->allocator, trace_event);
    if (trace_event->root != NULL && trace_event->event_array != NULL) {
        return AWS_OP_ERR;
    }
    return AWS_OP_SUCCESS;
}

int aws_trace_event_new(char *category, char *name, char phase) {
    /* set timestamp in milliseconds */
    uint64_t timestamp;
    aws_high_res_clock_get_ticks(&timestamp);
    timestamp -= start_time;
    timestamp = aws_timestamp_convert(timestamp, AWS_TIMESTAMP_NANOS, AWS_TIMESTAMP_MILLIS, 0);

    /* get calling thread and process ids */
    uint64_t thread_id = (uint64_t)aws_thread_current_thread_id();
    int process_id = aws_get_pid();

    struct aws_trace_event_metadata trace_event_data = {
        .phase = phase,
        .timestamp = timestamp,
        .thread_id = thread_id,
        .process_id = process_id,
    };
    trace_event_data.name = aws_mem_acquire(trace_event->allocator, ((sizeof(char) * strlen(name)) + 1));
    trace_event_data.category = aws_mem_acquire(trace_event->allocator, ((sizeof(char) * strlen(category)) + 1));
    strcpy(trace_event_data.name, name);
    strcpy(trace_event_data.category, category);

    /* send to the bus */
    aws_bus_send(&(trace_event->bus), listener_id, &trace_event_data, aws_trace_event_destroy);
    return 0;
}

struct cJSON *aws_trace_event_get_root() {
    return trace_event->root;
}
