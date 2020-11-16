/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */
#include <aws/common/thread.h>

#include <aws/common/clock.h>
#include <aws/common/logging.h>

#include <Windows.h>

#include <inttypes.h>

static struct aws_thread_options s_default_options = {
    /* zero will make sure whatever the default for that version of windows is used. */
    .stack_size = 0,
};

struct thread_atexit_callback {
    aws_thread_atexit_fn *callback;
    void *user_data;
    struct thread_atexit_callback *next;
};

struct thread_wrapper {
    struct aws_allocator *allocator;
    void (*func)(void *arg);
    void *arg;
    struct thread_atexit_callback *atexit;
};

static AWS_THREAD_LOCAL struct thread_wrapper *tl_wrapper = NULL;

static DWORD WINAPI thread_wrapper_fn(LPVOID arg) {
    struct thread_wrapper thread_wrapper = *(struct thread_wrapper *)arg;
    struct aws_allocator *allocator = thread_wrapper.allocator;
    tl_wrapper = &thread_wrapper;
    thread_wrapper.func(thread_wrapper.arg);

    struct thread_atexit_callback *exit_callback_data = thread_wrapper.atexit;
    aws_mem_release(allocator, arg);

    while (exit_callback_data) {
        aws_thread_atexit_fn *exit_callback = exit_callback_data->callback;
        void *exit_callback_user_data = exit_callback_data->user_data;
        struct thread_atexit_callback *next_exit_callback_data = exit_callback_data->next;

        aws_mem_release(allocator, exit_callback_data);

        exit_callback(exit_callback_user_data);
        exit_callback_data = next_exit_callback_data;
    }
    tl_wrapper = NULL;

    return 0;
}

const struct aws_thread_options *aws_default_thread_options(void) {
    return &s_default_options;
}

struct callback_fn_wrapper {
    void (*call_once)(void *);
    void *user_data;
};

BOOL WINAPI s_init_once_wrapper(PINIT_ONCE init_once, void *param, void **context) {
    (void)context;
    (void)init_once;

    struct callback_fn_wrapper *callback_fn_wrapper = param;
    callback_fn_wrapper->call_once(callback_fn_wrapper->user_data);
    return TRUE;
}

void aws_thread_call_once(aws_thread_once *flag, void (*call_once)(void *), void *user_data) {
    struct callback_fn_wrapper wrapper;
    wrapper.call_once = call_once;
    wrapper.user_data = user_data;
    InitOnceExecuteOnce((PINIT_ONCE)flag, s_init_once_wrapper, &wrapper, NULL);
}

int aws_thread_init(struct aws_thread *thread, struct aws_allocator *allocator) {
    thread->thread_handle = 0;
    thread->thread_id = 0;
    thread->allocator = allocator;
    thread->detach_state = AWS_THREAD_NOT_CREATED;

    return AWS_OP_SUCCESS;
}

/* windows is weird because apparently no one ever considered computers having more than 64 processors. Instead they
   have processor groups per process. We need to find the mask in the correct group. */
static void s_get_group_and_cpu_id(uint32_t desired_cpu, uint16_t *group, uint8_t *proc_num) {
    unsigned group_count = GetActiveProcessorGroupCount();

    unsigned total_processors_detected = 0;
    uint8_t group_with_desired_processor = 0;
    uint8_t group_mask_for_desired_processor = 0;

    /* for each group, keep counting til we find the group and the processor mask */
    for (uint8_t i = 0; i < group_count; ++group_count) {
        DWORD processor_count_in_group = GetActiveProcessorCount((WORD)i);
        if (total_processors_detected + processor_count_in_group > desired_cpu) {
            group_with_desired_processor = i;
            group_mask_for_desired_processor = (uint8_t)(desired_cpu - total_processors_detected);
            break;
        }
        total_processors_detected += processor_count_in_group;
    }

    *proc_num = group_mask_for_desired_processor;
    *group = group_with_desired_processor;
}

int aws_thread_launch(
    struct aws_thread *thread,
    void (*func)(void *arg),
    void *arg,
    const struct aws_thread_options *options) {

    SIZE_T stack_size = 0;

    if (options && options->stack_size > 0) {
        stack_size = (SIZE_T)options->stack_size;
    }

    struct thread_wrapper *thread_wrapper =
        (struct thread_wrapper *)aws_mem_calloc(thread->allocator, 1, sizeof(struct thread_wrapper));
    thread_wrapper->allocator = thread->allocator;
    thread_wrapper->arg = arg;
    thread_wrapper->func = func;

    thread->thread_handle =
        CreateThread(0, stack_size, thread_wrapper_fn, (LPVOID)thread_wrapper, 0, &thread->thread_id);

    if (!thread->thread_handle) {
        return aws_raise_error(AWS_ERROR_THREAD_INSUFFICIENT_RESOURCE);
    }

    if (options && options->cpu_id >= 0) {
        AWS_LOGF_INFO(
            AWS_LS_COMMON_THREAD,
            "id=%p: cpu affinity of cpu_id " PRIi32 " was specified, attempting to honor the value.",
            (void *)thread,
            options->cpu_id);

        uint16_t group = 0;
        uint8_t proc_num = 0;
        s_get_group_and_cpu_id(options->cpu_id, &group, &proc_num);
        GROUP_AFFINITY group_afinity;
        AWS_ZERO_STRUCT(group_afinity);
        group_afinity.Group = (WORD)group;
        group_afinity.Mask = (KAFFINITY)((uint64_t)1 << proc_num);
        AWS_LOGF_DEBUG(
            AWS_LS_COMMON_THREAD,
            "id=%p: computed mask " PRIx64 " on group " PRIu16 ".",
            (void *)thread,
            (uint64_t)group_afinity.Mask,
            (uint16_t)group_afinity.Group);

        BOOL set_group_val = SetThreadGroupAffinity(thread->thread_handle, &group_afinity, NULL);
        AWS_LOGF_DEBUG(
            AWS_LS_COMMON_THREAD,
            "id=%p: SetThreadGroupAffinity() result " PRIi8 ".",
            (void *)thread,
            (int8_t)set_group_val);

        if (set_group_val) {
            PROCESSOR_NUMBER processor_number;
            AWS_ZERO_STRUCT(processor_number);
            processor_number.Group = (WORD)group;
            processor_number.Number = proc_num;

            BOOL set_processor_val = SetThreadIdealProcessorEx(thread->thread_handle, &processor_number, NULL);
            AWS_LOGF_DEBUG(
                AWS_LS_COMMON_THREAD,
                "id=%p: SetThreadIdealProcessorEx() result " PRIi8 ".",
                (void *)thread,
                (int8_t)set_processor_val);
            if (!set_processor_val) {
                AWS_LOGF_WARN(
                    AWS_LS_COMMON_THREAD,
                    "id=%p: SetThreadIdealProcessorEx() failed with " PRIx32 ".",
                    (void *)thread,
                    (uint32_t)GetLastError());
            }
        } else {
            AWS_LOGF_WARN(
                AWS_LS_COMMON_THREAD,
                "id=%p: SetThreadGroupAffinity() failed with " PRIx32 ".",
                (void *)thread,
                (uint32_t)GetLastError());
        }
    }

    thread->detach_state = AWS_THREAD_JOINABLE;
    return AWS_OP_SUCCESS;
}

aws_thread_id_t aws_thread_get_id(struct aws_thread *thread) {
    return thread->thread_id;
}

enum aws_thread_detach_state aws_thread_get_detach_state(struct aws_thread *thread) {
    return thread->detach_state;
}

int aws_thread_join(struct aws_thread *thread) {
    if (thread->detach_state == AWS_THREAD_JOINABLE) {
        WaitForSingleObject(thread->thread_handle, INFINITE);
        thread->detach_state = AWS_THREAD_JOIN_COMPLETED;
    }

    return AWS_OP_SUCCESS;
}

void aws_thread_clean_up(struct aws_thread *thread) {
    CloseHandle(thread->thread_handle);
    thread->thread_handle = 0;
}

aws_thread_id_t aws_thread_current_thread_id(void) {
    return GetCurrentThreadId();
}

bool aws_thread_thread_id_equal(aws_thread_id_t t1, aws_thread_id_t t2) {
    return t1 == t2;
}

void aws_thread_current_sleep(uint64_t nanos) {
    /* We don't really have a better option here for windows that isn't super
     * complex AND we don't have a use case yet where we should have sleeps
     * anywhere other than for context switches and testing. When that time
     * arises put the effort in here. */
    Sleep((DWORD)aws_timestamp_convert(nanos, AWS_TIMESTAMP_NANOS, AWS_TIMESTAMP_MILLIS, NULL));
}

int aws_thread_current_at_exit(aws_thread_atexit_fn *callback, void *user_data) {
    if (!tl_wrapper) {
        return aws_raise_error(AWS_ERROR_THREAD_NOT_JOINABLE);
    }

    struct thread_atexit_callback *cb = aws_mem_calloc(tl_wrapper->allocator, 1, sizeof(struct thread_atexit_callback));
    if (!cb) {
        return AWS_OP_ERR;
    }
    cb->callback = callback;
    cb->user_data = user_data;
    cb->next = tl_wrapper->atexit;
    tl_wrapper->atexit = cb;
    return AWS_OP_SUCCESS;
}
