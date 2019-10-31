/*
 * Copyright 2019 Amazon.com, Inc. or its affiliates. All Rights Reserved.
 *
 * Licensed under the Apache License, Version 2.0 (the "License").
 * You may not use this file except in compliance with the License.
 * A copy of the License is located at
 *
 *  http://aws.amazon.com/apache2.0
 *
 * or in the "license" file accompanying this file. This file is distributed
 * on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 * express or implied. See the License for the specific language governing
 * permissions and limitations under the License.
 */
#if defined(AWS_HAVE_EXECINFO)
#    define ALLOC_TRACE_AVAILABLE
#    include <execinfo.h>
#    include <limits.h>
#endif

#include <aws/common/atomics.h>
#include <aws/common/byte_buf.h>
#include <aws/common/hash_table.h>
#include <aws/common/mutex.h>
#include <aws/common/priority_queue.h>
#include <aws/common/string.h>
#include <aws/common/system_info.h>
#include <aws/common/time.h>

/* describes a single live allocation */
struct alloc_t {
    size_t size;
    time_t time;
    uint64_t stack; /* hash of stack frame pointers */
};

/* one of these is stored per unique stack */
struct stacktrace_t {
    void *const frames[1]; /* rest of frames are allocated after */
};

/* Tracking structure, used as the allocator impl */
struct alloc_tracer {
    struct aws_allocator *allocator; /* underlying allocator */
    enum aws_mem_trace_level level;  /* level to trace at */
    size_t frames_per_stack;         /* how many frames to keep per stack */
    struct aws_atomic_var allocated; /* bytes currently allocated */
    struct aws_mutex mutex;          /* protects everything below */
    struct aws_hash_table allocs;    /* live allocations, maps address -> alloc_t */
    struct aws_hash_table stacks;    /* unique stack traces, maps hash -> stacktrace_t */
};

/* number of frames to skip in call stacks (s_alloc_tracer_track, and the vtable function) */
#define FRAMES_TO_SKIP 2

static void *s_trace_mem_acquire(struct aws_allocator *allocator, size_t size);
static void s_trace_mem_release(struct aws_allocator *allocator, void *ptr);
static void *s_trace_mem_realloc(struct aws_allocator *allocator, void *ptr, size_t old_size, size_t new_size);
static void *s_trace_mem_calloc(struct aws_allocator *allocator, size_t num, size_t size);

static struct aws_allocator s_trace_allocator = {
    .mem_acquire = s_trace_mem_acquire,
    .mem_release = s_trace_mem_release,
    .mem_realloc = s_trace_mem_realloc,
    .mem_calloc = s_trace_mem_calloc,
};

/* for the hash table, to destroy elements */
static void s_destroy_alloc(void *data) {
    struct aws_allocator *allocator = aws_default_allocator();
    struct alloc_t *alloc = data;
    aws_mem_release(allocator, alloc);
}

static void s_destroy_stacktrace(void *data) {
    struct aws_allocator *allocator = aws_default_allocator();
    struct stacktrace_t *stack = data;
    aws_mem_release(allocator, stack);
}

static uint64_t s_stack_hash(const void *item) {
    /* yes, this truncates on 32-bit, no it doesn't matter, it's a hash */
    size_t value = (size_t)item;
    return aws_hash_ptr((void *)value);
}

static bool s_stack_eq(const void *a, const void *b) {
    uint64_t va = (uint64_t)a;
    uint64_t vb = (uint64_t)b;
    return va == vb;
}

static void s_alloc_tracer_init(
    struct alloc_tracer *tracer,
    struct aws_allocator *allocator,
    enum aws_mem_trace_level level,
    size_t frames_per_stack) {
    tracer->allocator = allocator;
    tracer->level = level;
    
    if (tracer->level >= AWS_MEMTRACE_BYTES) {
        aws_atomic_init_int(&tracer->allocated, 0);
        AWS_FATAL_ASSERT(AWS_OP_SUCCESS == aws_mutex_init(&tracer->mutex));
        AWS_FATAL_ASSERT(
            AWS_OP_SUCCESS ==
            aws_hash_table_init(
                &tracer->allocs, tracer->allocator, 1024, aws_hash_ptr, aws_ptr_eq, NULL, s_destroy_alloc));
    }
    
    if (tracer->level == AWS_MEMTRACE_STACKS) {
        tracer->frames_per_stack = (frames_per_stack) ? frames_per_stack : 8;
        AWS_FATAL_ASSERT(
            AWS_OP_SUCCESS ==
            aws_hash_table_init(
                &tracer->stacks, tracer->allocator, 1024, s_stack_hash, s_stack_eq, NULL, s_destroy_stacktrace));
    }
}

static void s_alloc_tracer_track(struct alloc_tracer *tracer, void *ptr, size_t size) {
    if (tracer->level == AWS_MEMTRACE_NONE) {
        return;
    }

    struct alloc_t *alloc = aws_mem_calloc(aws_default_allocator(), 1, sizeof(struct alloc_t));
    alloc->size = size;
    alloc->time = time(NULL);
    aws_atomic_fetch_add(&tracer->allocated, size);

#if defined(ALLOC_TRACE_AVAILABLE)
    if (tracer->level == AWS_MEMTRACE_STACKS) {
        /* capture stack frames, skip 2 for this function and the allocation vtable function */
        AWS_VARIABLE_LENGTH_ARRAY(void *, stack_frames, FRAMES_TO_SKIP + tracer->frames_per_stack);
        int stack_depth = backtrace(stack_frames, FRAMES_TO_SKIP + tracer->frames_per_stack);
        /* hash the stack pointers */
        struct aws_byte_cursor stack_cursor = aws_byte_cursor_from_array(stack_frames, stack_depth * sizeof(void *));
        uint64_t stack_id = aws_hash_byte_cursor_ptr(&stack_cursor);
        alloc->stack = stack_id; /* associate the stack with the alloc */

        aws_mutex_lock(&tracer->mutex);
        struct aws_hash_element *item = NULL;
        int was_created = 0;
        AWS_FATAL_ASSERT(
            AWS_OP_SUCCESS == aws_hash_table_create(&tracer->stacks, (void *)stack_id, &item, &was_created));
        /* If this is a new stack, save it to the hash */
        if (was_created) {
            struct stacktrace_t *stack = aws_mem_calloc(
                tracer->allocator, 1, sizeof(struct stacktrace_t) + (sizeof(void *) * (tracer->frames_per_stack - 1)));
            memcpy(
                (void **)&stack->frames[0],
                &stack_frames[FRAMES_TO_SKIP],
                (stack_depth - FRAMES_TO_SKIP) * sizeof(void *));
            item->value = stack;
        }
        aws_mutex_unlock(&tracer->mutex);
    }
#endif

    aws_mutex_lock(&tracer->mutex);
    AWS_FATAL_ASSERT(AWS_OP_SUCCESS == aws_hash_table_put(&tracer->allocs, ptr, alloc, NULL));
    aws_mutex_unlock(&tracer->mutex);
}

static void s_alloc_tracer_untrack(struct alloc_tracer *tracer, void *ptr) {
    if (tracer->level == AWS_MEMTRACE_NONE) {
        return;
    }

    aws_mutex_lock(&tracer->mutex);
    struct aws_hash_element *item;
    AWS_FATAL_ASSERT(AWS_OP_SUCCESS == aws_hash_table_find(&tracer->allocs, ptr, &item));
    AWS_FATAL_ASSERT(item->key == ptr && item->value);
    struct alloc_t *alloc = item->value;
    aws_atomic_fetch_sub(&tracer->allocated, alloc->size);
    s_destroy_alloc(item->value);
    AWS_FATAL_ASSERT(AWS_OP_SUCCESS == aws_hash_table_remove_element(&tracer->allocs, item));
    aws_mutex_unlock(&tracer->mutex);
}

#if defined(ALLOC_TRACE_AVAILABLE)
/* used only to resolve stacks -> trace, count, size at dump time */
struct stack_info_t {
    struct aws_string *trace;
    size_t count;
    size_t size;
};

static int s_collect_stack_trace(void *context, struct aws_hash_element *item) {
    struct alloc_tracer *tracer = context;
    struct aws_hash_table *all_stacks = &tracer->stacks;
    struct aws_allocator *allocator = aws_default_allocator();
    struct stack_info_t *stack_info = item->value;
    struct aws_hash_element *stack_item = NULL;
    AWS_FATAL_ASSERT(AWS_OP_SUCCESS == aws_hash_table_find(all_stacks, item->key, &stack_item));
    AWS_FATAL_ASSERT(stack_item);
    struct stacktrace_t *stack = stack_item->value;
    void *const *stack_frames = &stack->frames[0];
    size_t num_frames = 0;
    while (stack_frames[num_frames] != NULL && num_frames < tracer->frames_per_stack) {
        ++num_frames;
    }

    /* convert the frame pointers to symbols, and concat into a buffer */
    char buf[4096] = {0};
    struct aws_byte_buf stacktrace = aws_byte_buf_from_empty_array(buf, AWS_ARRAY_SIZE(buf));
    struct aws_byte_cursor newline = aws_byte_cursor_from_c_str("\n");
    char **symbols = backtrace_symbols(stack_frames, num_frames);
    for (int idx = 0; idx < num_frames; ++idx) {
        if (idx > 0) {
            aws_byte_buf_append(&stacktrace, &newline);
        }
        const char *caller = symbols[idx];
        if (!caller || !caller[0]) {
            break;
        }
        struct aws_byte_cursor cursor = aws_byte_cursor_from_c_str(caller);
        aws_byte_buf_append(&stacktrace, &cursor);
    }
    free(symbols);
    /* record the resultant buffer as a string */
    stack_info->trace = aws_string_new_from_array(allocator, stacktrace.buffer, stacktrace.len);
    aws_byte_buf_clean_up(&stacktrace);
    return AWS_COMMON_HASH_TABLE_ITER_CONTINUE;
}

static int s_stack_info_compare_size(const void *a, const void *b) {
    const struct stack_info_t *stack_a = *(const struct stack_info_t **)a;
    const struct stack_info_t *stack_b = *(const struct stack_info_t **)b;
    return stack_b->size > stack_a->size;
}

static int s_stack_info_compare_count(const void *a, const void *b) {
    const struct stack_info_t *stack_a = *(const struct stack_info_t **)a;
    const struct stack_info_t *stack_b = *(const struct stack_info_t **)b;
    return stack_b->count > stack_a->count;
}

static void s_stack_info_destroy(void *data) {
    struct aws_allocator *allocator = aws_default_allocator();
    struct stack_info_t *stack = data;
    aws_string_destroy(stack->trace);
    aws_mem_release(allocator, stack);
}

/* tally up count/size per stack from all allocs */
static int s_collect_stack_stats(void *context, struct aws_hash_element *item) {
    struct aws_hash_table *stacks = context;
    struct alloc_t *alloc = item->value;
    struct aws_hash_element *stack_item = NULL;
    int was_created = 0;
    AWS_FATAL_ASSERT(AWS_OP_SUCCESS == aws_hash_table_create(stacks, (void *)alloc->stack, &stack_item, &was_created));
    if (was_created) {
        struct aws_allocator *allocator = aws_default_allocator();
        stack_item->value = aws_mem_calloc(allocator, 1, sizeof(struct stack_info_t));
    }
    struct stack_info_t *stack = stack_item->value;
    stack->count++;
    stack->size += alloc->size;
    return AWS_COMMON_HASH_TABLE_ITER_CONTINUE;
}

static int s_insert_stacks(void *context, struct aws_hash_element *item) {
    struct aws_priority_queue *pq = context;
    struct stack_info_t *stack = item->value;
    AWS_FATAL_ASSERT(AWS_OP_SUCCESS == aws_priority_queue_push(pq, &stack));
    return AWS_COMMON_HASH_TABLE_ITER_CONTINUE;
}
#endif

static int s_insert_allocs(void *context, struct aws_hash_element *item) {
    struct aws_priority_queue *allocs = context;
    struct alloc_t *alloc = item->value;
    AWS_FATAL_ASSERT(AWS_OP_SUCCESS == aws_priority_queue_push(allocs, &alloc));
    return AWS_COMMON_HASH_TABLE_ITER_CONTINUE;
}

static int s_alloc_compare(const void *a, const void *b) {
    const struct alloc_t *alloc_a = *(const struct alloc_t **)a;
    const struct alloc_t *alloc_b = *(const struct alloc_t **)b;
    return alloc_a->time > alloc_b->time;
}

static void s_alloc_tracer_dump(struct alloc_tracer *tracer) {
    if (tracer->level == AWS_MEMTRACE_NONE || aws_atomic_load_int(&tracer->allocated) == 0) {
        return;
    }

    aws_mutex_lock(&tracer->mutex);

    size_t num_allocs = aws_hash_table_get_entry_count(&tracer->allocs);
    fprintf(
        stderr,
        "tracer: %zu bytes still allocated in %zu allocations\n",
        aws_atomic_load_int(&tracer->allocated),
        num_allocs);

#if defined(ALLOC_TRACE_AVAILABLE)
    /* convert stacks from pointers -> symbols */
    struct aws_hash_table stacks; /* maps stack hash/id -> stack_info_t */
    AWS_FATAL_ASSERT(
        AWS_OP_SUCCESS ==
        aws_hash_table_init(&stacks, tracer->allocator, 64, s_stack_hash, s_stack_eq, NULL, s_stack_info_destroy));
    /* collect active stacks, tally up sizes and counts */
    aws_hash_table_foreach(&tracer->allocs, s_collect_stack_stats, &stacks);
    /* collect stack traces for active stacks */
    aws_hash_table_foreach(&stacks, s_collect_stack_trace, tracer);
#endif

    /* sort allocs by time */
    struct aws_priority_queue allocs;
    aws_priority_queue_init_dynamic(&allocs, tracer->allocator, num_allocs, sizeof(struct alloc_t *), s_alloc_compare);
    aws_hash_table_foreach(&tracer->allocs, s_insert_allocs, &allocs);
    /* dump allocs by time */
    fprintf(stderr, "################################################################################\n");
    fprintf(stderr, "Leaks in order of allocation:\n");
    fprintf(stderr, "################################################################################\n");
    while (aws_priority_queue_size(&allocs)) {
        struct alloc_t *alloc = NULL;
        aws_priority_queue_pop(&allocs, &alloc);
        fprintf(stderr, "ALLOC %zu bytes\n", alloc->size);
#if defined(ALLOC_TRACE_AVAILABLE)
        if (alloc->stack) {
            struct aws_hash_element *item = NULL;
            AWS_FATAL_ASSERT(AWS_OP_SUCCESS == aws_hash_table_find(&stacks, (void *)alloc->stack, &item));
            struct stack_info_t *stack = item->value;
            fprintf(stderr, "  stacktrace:\n%s\n", (const char *)aws_string_bytes(stack->trace));
        }
#endif
    }

    aws_priority_queue_clean_up(&allocs);

#if defined(ALLOC_TRACE_AVAILABLE)
    size_t num_stacks = aws_hash_table_get_entry_count(&stacks);
    /* sort stacks by total size leaked */
    struct aws_priority_queue stacks_by_size;
    AWS_FATAL_ASSERT(
        AWS_OP_SUCCESS ==
        aws_priority_queue_init_dynamic(
            &stacks_by_size, tracer->allocator, num_stacks, sizeof(struct stack_info_t *), s_stack_info_compare_size));
    aws_hash_table_foreach(&stacks, s_insert_stacks, &stacks_by_size);
    fprintf(stderr, "################################################################################\n");
    fprintf(stderr, "Stacks by bytes leaked:\n");
    fprintf(stderr, "################################################################################\n");
    while (aws_priority_queue_size(&stacks_by_size) > 0) {
        struct stack_info_t *stack = NULL;
        aws_priority_queue_pop(&stacks_by_size, &stack);
        fprintf(stderr, "%zu bytes in %zu allocations:\n", stack->size, stack->count);
        fprintf(stderr, "%s\n", (const char *)aws_string_bytes(stack->trace));
    }
    aws_priority_queue_clean_up(&stacks_by_size);

    /* sort stacks by number of leaks */
    struct aws_priority_queue stacks_by_count;
    AWS_FATAL_ASSERT(
        AWS_OP_SUCCESS == aws_priority_queue_init_dynamic(
                              &stacks_by_count,
                              tracer->allocator,
                              num_stacks,
                              sizeof(struct stack_info_t *),
                              s_stack_info_compare_count));
    fprintf(stderr, "################################################################################\n");
    fprintf(stderr, "Stacks by number of leaks:\n");
    fprintf(stderr, "################################################################################\n");
    aws_hash_table_foreach(&stacks, s_insert_stacks, &stacks_by_count);
    while (aws_priority_queue_size(&stacks_by_count) > 0) {
        struct stack_info_t *stack = NULL;
        aws_priority_queue_pop(&stacks_by_count, &stack);
        fprintf(stderr, "%zu allocations leaking %zu bytes:\n", stack->count, stack->size);
        fprintf(stderr, "%s\n", (const char *)aws_string_bytes(stack->trace));
    }
    aws_priority_queue_clean_up(&stacks_by_count);
    aws_hash_table_clean_up(&stacks);
#endif

    fflush(stderr);
    aws_mutex_unlock(&tracer->mutex);
    // abort();
}

static void *s_trace_mem_acquire(struct aws_allocator *allocator, size_t size) {
    struct alloc_tracer *tracer = allocator->impl;
    void *ptr = aws_mem_acquire(tracer->allocator, size);
    s_alloc_tracer_track(tracer, ptr, size);
    return ptr;
}

static void s_trace_mem_release(struct aws_allocator *allocator, void *ptr) {
    struct alloc_tracer *tracer = allocator->impl;
    s_alloc_tracer_untrack(tracer, ptr);
    aws_mem_release(tracer->allocator, ptr);
}

static void *s_trace_mem_realloc(struct aws_allocator *allocator, void *ptr, size_t old_size, size_t new_size) {
    struct alloc_tracer *tracer = allocator->impl;
    void *new_ptr = ptr;

    AWS_FATAL_ASSERT(AWS_OP_SUCCESS == aws_mem_realloc(tracer->allocator, &new_ptr, old_size, new_size));

    s_alloc_tracer_untrack(tracer, ptr);
    s_alloc_tracer_track(tracer, new_ptr, new_size);

    return new_ptr;
}

static void *s_trace_mem_calloc(struct aws_allocator *allocator, size_t num, size_t size) {
    struct alloc_tracer *tracer = allocator->impl;
    void *ptr = aws_mem_calloc(tracer->allocator, num, size);
    s_alloc_tracer_track(tracer, ptr, num * size);
    return ptr;
}

struct aws_allocator *aws_mem_tracer_new(
    struct aws_allocator *allocator,
    enum aws_mem_trace_level level,
    size_t frames_per_stack) {
    struct aws_allocator *trace_allocator = aws_mem_calloc(aws_default_allocator(), 1, sizeof(struct aws_allocator));
    AWS_FATAL_ASSERT(trace_allocator);
    struct alloc_tracer *tracer = aws_mem_calloc(aws_default_allocator(), 1, sizeof(struct alloc_tracer));
    AWS_FATAL_ASSERT(tracer);

    /* copy the template vtable s*/
    *trace_allocator = s_trace_allocator;
    trace_allocator->impl = tracer;
#if !defined(ALLOC_TRACE_AVAILABLE)
    /* clamp level if tracing isn't available */
    level = level > AWS_MEMTRACE_BYTES ? AWS_MEMTRACE_BYTES : level;
#endif
    s_alloc_tracer_init(tracer, allocator, level, frames_per_stack);
    return trace_allocator;
}

struct aws_allocator *aws_mem_tracer_destroy(struct aws_allocator *tracer_allocator) {
    struct alloc_tracer *tracer = tracer_allocator->impl;
    struct aws_allocator *allocator = tracer->allocator;

    /* This is not necessary, as if you are destroying the allocator, what are your
     * expectations? Either way, we can, so we might as well...
     */
    aws_mutex_lock(&tracer->mutex);
    aws_hash_table_clean_up(&tracer->allocs);
    aws_hash_table_clean_up(&tracer->stacks);
    aws_mutex_unlock(&tracer->mutex);
    aws_mutex_clean_up(&tracer->mutex);

    aws_mem_release(aws_default_allocator(), tracer);
    aws_mem_release(aws_default_allocator(), tracer_allocator);
    return allocator;
}

void aws_mem_trace_dump(struct aws_allocator *trace_allocator) {
    struct alloc_tracer *tracer = trace_allocator->impl;
    s_alloc_tracer_dump(tracer);
}

size_t aws_mem_tracer_count(struct aws_allocator *trace_allocator) {
    struct alloc_tracer *tracer = trace_allocator->impl;
    return aws_atomic_load_int(&tracer->allocated);
}
