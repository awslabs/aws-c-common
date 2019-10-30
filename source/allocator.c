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

#include <aws/common/assert.h>
#include <aws/common/common.h>
#include <aws/common/logging.h>
#include <aws/common/math.h>

#include <stdarg.h>
#include <stdlib.h>

#ifdef _WIN32
#    include <Windows.h>
#endif

#ifdef __MACH__
#    include <CoreFoundation/CoreFoundation.h>
#endif

/* turn off unused named parameter warning on msvc.*/
#ifdef _MSC_VER
#    pragma warning(push)
#    pragma warning(disable : 4100)
#endif

bool aws_allocator_is_valid(const struct aws_allocator *alloc) {
    /* An allocator must define mem_acquire and mem_release.  All other fields are optional */
    return alloc && AWS_OBJECT_PTR_IS_READABLE(alloc) && alloc->mem_acquire && alloc->mem_release;
}

static void *s_default_malloc(struct aws_allocator *allocator, size_t size) {
    (void)allocator;
    return malloc(size);
}

static void s_default_free(struct aws_allocator *allocator, void *ptr) {
    (void)allocator;
    free(ptr);
}

static void *s_default_realloc(struct aws_allocator *allocator, void *ptr, size_t oldsize, size_t newsize) {
    (void)allocator;
    (void)oldsize;
    return realloc(ptr, newsize);
}

static void *s_default_calloc(struct aws_allocator *allocator, size_t num, size_t size) {
    (void)allocator;
    return calloc(num, size);
}

static struct aws_allocator default_allocator = {
    .mem_acquire = s_default_malloc,
    .mem_release = s_default_free,
    .mem_realloc = s_default_realloc,
    .mem_calloc = s_default_calloc,
};

struct aws_allocator *aws_default_allocator(void) {
    return &default_allocator;
}

void *aws_mem_acquire(struct aws_allocator *allocator, size_t size) {
    AWS_FATAL_PRECONDITION(allocator != NULL);
    AWS_FATAL_PRECONDITION(allocator->mem_acquire != NULL);
    /* Protect against https://wiki.sei.cmu.edu/confluence/display/c/MEM04-C.+Beware+of+zero-length+allocations */
    AWS_FATAL_PRECONDITION(size != 0);

    void *mem = allocator->mem_acquire(allocator, size);
    if (!mem) {
        aws_raise_error(AWS_ERROR_OOM);
    }
    return mem;
}

void *aws_mem_calloc(struct aws_allocator *allocator, size_t num, size_t size) {
    AWS_FATAL_PRECONDITION(allocator != NULL);
    AWS_FATAL_PRECONDITION(allocator->mem_calloc || allocator->mem_acquire);
    /* Protect against https://wiki.sei.cmu.edu/confluence/display/c/MEM04-C.+Beware+of+zero-length+allocations */
    AWS_FATAL_PRECONDITION(num != 0 && size != 0);

    /* Defensive check: never use calloc with size * num that would overflow
     * https://wiki.sei.cmu.edu/confluence/display/c/MEM07-C.+Ensure+that+the+arguments+to+calloc%28%29%2C+when+multiplied%2C+do+not+wrap
     */
    size_t required_bytes;
    if (aws_mul_size_checked(num, size, &required_bytes)) {
        return NULL;
    }

    /* If there is a defined calloc, use it */
    if (allocator->mem_calloc) {
        void *mem = allocator->mem_calloc(allocator, num, size);
        if (!mem) {
            aws_raise_error(AWS_ERROR_OOM);
        }
        return mem;
    }

    /* Otherwise, emulate calloc */
    void *mem = allocator->mem_acquire(allocator, required_bytes);
    if (!mem) {
        aws_raise_error(AWS_ERROR_OOM);
        return NULL;
    }
    memset(mem, 0, required_bytes);
    AWS_POSTCONDITION(mem != NULL);
    return mem;
}

#define AWS_ALIGN_ROUND_UP(value, alignment) (((value) + ((alignment)-1)) & ~((alignment)-1))

void *aws_mem_acquire_many(struct aws_allocator *allocator, size_t count, ...) {

    enum { S_ALIGNMENT = sizeof(intmax_t) };

    va_list args_size;
    va_start(args_size, count);
    va_list args_allocs;
    va_copy(args_allocs, args_size);

    size_t total_size = 0;
    for (size_t i = 0; i < count; ++i) {

        /* Ignore the pointer argument for now */
        va_arg(args_size, void **);

        size_t alloc_size = va_arg(args_size, size_t);
        total_size += AWS_ALIGN_ROUND_UP(alloc_size, S_ALIGNMENT);
    }
    va_end(args_size);

    void *allocation = NULL;

    if (total_size > 0) {

        allocation = aws_mem_acquire(allocator, total_size);
        if (!allocation) {
            aws_raise_error(AWS_ERROR_OOM);
            goto cleanup;
        }

        uint8_t *current_ptr = allocation;

        for (size_t i = 0; i < count; ++i) {

            void **out_ptr = va_arg(args_allocs, void **);

            size_t alloc_size = va_arg(args_allocs, size_t);
            alloc_size = AWS_ALIGN_ROUND_UP(alloc_size, S_ALIGNMENT);

            *out_ptr = current_ptr;
            current_ptr += alloc_size;
        }
    }

cleanup:
    va_end(args_allocs);
    return allocation;
}

#undef AWS_ALIGN_ROUND_UP

void aws_mem_release(struct aws_allocator *allocator, void *ptr) {
    AWS_FATAL_PRECONDITION(allocator != NULL);
    AWS_FATAL_PRECONDITION(allocator->mem_release != NULL);

    if (ptr != NULL) {
        allocator->mem_release(allocator, ptr);
    }
}

int aws_mem_realloc(struct aws_allocator *allocator, void **ptr, size_t oldsize, size_t newsize) {
    AWS_FATAL_PRECONDITION(allocator != NULL);
    AWS_FATAL_PRECONDITION(allocator->mem_realloc || allocator->mem_acquire);
    AWS_FATAL_PRECONDITION(allocator->mem_release);

    /* Protect against https://wiki.sei.cmu.edu/confluence/display/c/MEM04-C.+Beware+of+zero-length+allocations */
    if (newsize == 0) {
        aws_mem_release(allocator, *ptr);
        *ptr = NULL;
        return AWS_OP_SUCCESS;
    }

    if (allocator->mem_realloc) {
        void *newptr = allocator->mem_realloc(allocator, *ptr, oldsize, newsize);
        if (!newptr) {
            return aws_raise_error(AWS_ERROR_OOM);
        }
        *ptr = newptr;
        return AWS_OP_SUCCESS;
    }

    /* Since the allocator doesn't support realloc, we'll need to emulate it (inefficiently). */
    if (oldsize >= newsize) {
        return AWS_OP_SUCCESS;
    }

    void *newptr = allocator->mem_acquire(allocator, newsize);
    if (!newptr) {
        return aws_raise_error(AWS_ERROR_OOM);
    }

    memcpy(newptr, *ptr, oldsize);
    memset((uint8_t *)newptr + oldsize, 0, newsize - oldsize);

    aws_mem_release(allocator, *ptr);

    *ptr = newptr;

    return AWS_OP_SUCCESS;
}

/* Wraps a CFAllocator around aws_allocator. For Mac only. */
#ifdef __MACH__

static CFStringRef s_cf_allocator_description = CFSTR("CFAllocator wrapping aws_allocator.");

/* note we don't have a standard specification stating sizeof(size_t) == sizeof(void *) so we have some extra casts */
static void *s_cf_allocator_allocate(CFIndex alloc_size, CFOptionFlags hint, void *info) {
    (void)hint;

    struct aws_allocator *allocator = info;

    void *mem = aws_mem_acquire(allocator, (size_t)alloc_size + sizeof(size_t));

    if (!mem) {
        return NULL;
    }

    size_t allocation_size = (size_t)alloc_size + sizeof(size_t);
    memcpy(mem, &allocation_size, sizeof(size_t));
    return (void *)((uint8_t *)mem + sizeof(size_t));
}

static void s_cf_allocator_deallocate(void *ptr, void *info) {
    struct aws_allocator *allocator = info;

    void *original_allocation = (uint8_t *)ptr - sizeof(size_t);

    aws_mem_release(allocator, original_allocation);
}

static void *s_cf_allocator_reallocate(void *ptr, CFIndex new_size, CFOptionFlags hint, void *info) {
    (void)hint;

    struct aws_allocator *allocator = info;
    AWS_ASSERT(allocator->mem_realloc);

    void *original_allocation = (uint8_t *)ptr - sizeof(size_t);
    size_t original_size = 0;
    memcpy(&original_size, original_allocation, sizeof(size_t));

    if (aws_mem_realloc(allocator, &original_allocation, original_size, (size_t)new_size)) {
        return NULL;
    }

    size_t new_allocation_size = (size_t)new_size;
    memcpy(original_allocation, &new_allocation_size, sizeof(size_t));

    return (void *)((uint8_t *)original_allocation + sizeof(size_t));
}

static CFStringRef s_cf_allocator_copy_description(const void *info) {
    (void)info;

    return s_cf_allocator_description;
}

static CFIndex s_cf_allocator_preferred_size(CFIndex size, CFOptionFlags hint, void *info) {
    (void)hint;
    (void)info;

    return size + sizeof(size_t);
}

CFAllocatorRef aws_wrapped_cf_allocator_new(struct aws_allocator *allocator) {
    CFAllocatorRef cf_allocator = NULL;

    CFAllocatorReallocateCallBack reallocate_callback = NULL;

    if (allocator->mem_realloc) {
        reallocate_callback = s_cf_allocator_reallocate;
    }

    CFAllocatorContext context = {
        .allocate = s_cf_allocator_allocate,
        .copyDescription = s_cf_allocator_copy_description,
        .deallocate = s_cf_allocator_deallocate,
        .reallocate = reallocate_callback,
        .info = allocator,
        .preferredSize = s_cf_allocator_preferred_size,
        .release = NULL,
        .retain = NULL,
        .version = 0,
    };

    cf_allocator = CFAllocatorCreate(NULL, &context);

    if (!cf_allocator) {
        aws_raise_error(AWS_ERROR_OOM);
    }

    return cf_allocator;
}

void aws_wrapped_cf_allocator_destroy(CFAllocatorRef allocator) {
    CFRelease(allocator);
}

#endif /*__MACH__ */

/******************************************************************************
 * MEMORY TRACING
 ******************************************************************************/ 
#if defined(AWS_HAVE_EXECINFO)
#    define ALLOC_TRACE_AVAILABLE
#    include <execinfo.h>
#    include <limits.h>
#endif

#include <aws/common/atomics.h>
#include <aws/common/hash_table.h>
#include <aws/common/mutex.h>
#include <aws/common/priority_queue.h>
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

static void s_alloc_tracer_init(struct alloc_tracer *tracer, struct aws_allocator *allocator, enum aws_mem_trace_level level, size_t frames_per_stack) {
    tracer->allocator = allocator;
    tracer->level = level;
    tracer->frames_per_stack = frames_per_stack;
    aws_atomic_init_int(&tracer->allocated, 0);
    AWS_FATAL_ASSERT(AWS_OP_SUCCESS == aws_mutex_init(&tracer->mutex));
    AWS_FATAL_ASSERT(
        AWS_OP_SUCCESS ==
        aws_hash_table_init(
            &tracer->allocs, tracer->allocator, 1024, aws_hash_ptr, aws_ptr_eq, NULL, s_destroy_alloc));
    if (tracer->level == AWS_MEMTRACE_STACKS) {
        AWS_FATAL_ASSERT(
            AWS_OP_SUCCESS ==
            aws_hash_table_init(
                &tracer->stacks, tracer->allocator, 1024, s_stack_hash, s_stack_eq, NULL, s_destroy_stacktrace));
    }
}

static void s_alloc_tracer_track(struct alloc_tracer *tracer, void *ptr, size_t size) {
    struct alloc_t *alloc = aws_mem_calloc(tracer->allocator, 1, sizeof(struct alloc_t));
    alloc->size = size;
    alloc->time = time(NULL);
    aws_atomic_fetch_add(&tracer->allocated, size);

#if defined(ALLOC_TRACE_AVAILABLE)
    if (s_memory_tracing == 2) {
        /* capture stack frames, skip 2 for this function and the allocation vtable function */
        AWS_VARIABLE_LENGTH_ARRAY(void *, stack_frames, 2 + tracer->frames_per_stack);
        int stack_depth = backtrace(stack_frames, 2 + tracer->frames_per_stack);
        /* hash the stack pointers */
        struct aws_byte_cursor stack_cursor = aws_byte_cursor_from_array(stack_frames, stack_depth * sizeof(void *));
        uint64_t stack_id = aws_hash_byte_cursor_ptr(&stack_cursor);
        alloc->stack = stack_id; /* associate the stack with the alloc */
        struct aws_hash_element *item = NULL;
        aws_mutex_lock(&tracer->mutex);
        int was_created = 0;
        AWS_FATAL_ASSERT(
            AWS_OP_SUCCESS == aws_hash_table_create(&tracer->stacks, (void *)stack_id, &item, &was_created));
        /* If this is a new stack, save it to the hash */
        if (was_created) {
            struct stacktrace_t *stack = aws_mem_calloc(tracer->allocator, 1, sizeof(struct stacktrace_t) + (sizeof(void*) * (tracer->frames_per_stack - 1)));
            memcpy((void **)&stack->frames[0], &stack_frames[2], (stack_depth - 2) * sizeof(void *));
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
    aws_mutex_lock(&tracer->mutex);
    struct aws_hash_element item;
    AWS_FATAL_ASSERT(AWS_OP_SUCCESS == aws_hash_table_remove(&tracer->allocs, ptr, &item, NULL));
    AWS_FATAL_ASSERT(item.key && item.value);
    struct alloc_t *alloc = item.value;
    aws_mutex_unlock(&tracer->mutex);

    aws_atomic_fetch_sub(&tracer->allocated, alloc->size);
    s_destroy_alloc(item.value);
}

#if defined(ALLOC_TRACE_AVAILABLE)
/* used only to resolve stacks -> trace, count, size at dump time */
struct stack_info_t {
    struct aws_string *trace;
    size_t count;
    size_t size;
};

static int s_collect_stack_trace(void *context, struct aws_hash_element *item) {
    struct aws_hash_table *all_stacks = context;
    struct aws_allocator *allocator = aws_default_allocator();
    struct stack_info_t *stack_info = item->value;
    struct aws_hash_element *stack_item = NULL;
    AWS_FATAL_ASSERT(AWS_OP_SUCCESS == aws_hash_table_find(all_stacks, item->key, &stack_item));
    AWS_FATAL_ASSERT(stack_item);
    struct stacktrace_t *stack = stack_item->value;
    void *const *stack_frames = &stack->frames[0];
    size_t num_frames = 0;
    while (stack_frames[num_frames] != NULL && num_frames < ALLOC_TRACING_FRAMES) {
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
    if (aws_atomic_load_int(&tracer->allocated) == 0) {
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
    aws_hash_table_foreach(&stacks, s_collect_stack_trace, &tracer->stacks);
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

struct aws_allocator *aws_mem_trace(struct aws_allocator *allocator, enum aws_mem_trace_level level, size_t frames_per_stack) {
    struct aws_allocator *trace_allocator = aws_mem_calloc(aws_default_allocator(), 1, sizeof(struct aws_allocator));
    AWS_FATAL_ASSERT(trace_allocator);
    struct alloc_tracer *tracer = aws_mem_calloc(aws_default_allocator(), 1, sizeof(struct alloc_tracer));
    AWS_FATAL_ASSERT(tracer);

    /* copy the template vtable s*/
    *trace_allocator = s_trace_allocator;
    trace_allocator->impl = tracer;
#if defined(ALLOC_TRACE_AVAILABLE)
    /* clamp level if tracing isn't available */
    level = level > AWS_MEMTRACE_BYTES ? AWS_MEMTRACE_BYTES : level;
#endif
    s_alloc_tracer_init(tracer, allocator, level, frames_per_stack);
    return trace_allocator;
}

void aws_mem_trace_dump(struct aws_allocator *trace_allocator) {
    struct alloc_tracer *tracer = trace_allocator->impl;
    s_alloc_tracer_dump(tracer);
}
