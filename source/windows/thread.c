/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */
#include <aws/common/thread.h>

#include <aws/common/clock.h>
#include <aws/common/linked_list.h>
#include <aws/common/logging.h>
#include <aws/common/private/thread_shared.h>
#include <aws/common/string.h>

#include <windows.h>

#include <inttypes.h>

/* Convert a string from a macro to a wide string */
#define WIDEN2(s) L## #s
#define WIDEN(s) WIDEN2(s)

static struct aws_thread_options s_default_options = {
    /* zero will make sure whatever the default for that version of windows is used. */
    .stack_size = 0,
    .cpu_id = -1,
    .join_strategy = AWS_TJS_MANUAL,
};

struct thread_atexit_callback {
    aws_thread_atexit_fn *callback;
    void *user_data;
    struct thread_atexit_callback *next;
};

struct thread_wrapper {
    struct aws_allocator *allocator;
    struct aws_linked_list_node node;
    void (*func)(void *arg);
    void *arg;
    struct thread_atexit_callback *atexit;

    /*
     * The managed thread system does lazy joins on threads once finished via their wrapper.  For that to work
     * we need something to join against, so we keep a by-value copy of the original thread here.  The tricky part
     * is how to set the threadid/handle of this copy since the copy must be injected into the thread function before
     * the threadid/handle is known.  We get around that by just querying it at the top of the wrapper thread function.
     */
    struct aws_thread thread_copy;
};

static AWS_THREAD_LOCAL struct thread_wrapper *tl_wrapper = NULL;

/*
 * thread_wrapper is platform-dependent so this function ends up being duplicated in each thread implementation
 */
void aws_thread_join_and_free_wrapper_list(struct aws_linked_list *wrapper_list) {
    struct aws_linked_list_node *iter = aws_linked_list_begin(wrapper_list);
    while (iter != aws_linked_list_end(wrapper_list)) {

        struct thread_wrapper *join_thread_wrapper = AWS_CONTAINER_OF(iter, struct thread_wrapper, node);
        iter = aws_linked_list_next(iter);
        join_thread_wrapper->thread_copy.detach_state = AWS_THREAD_JOINABLE;
        aws_thread_join(&join_thread_wrapper->thread_copy);
        aws_thread_clean_up(&join_thread_wrapper->thread_copy);
        aws_mem_release(join_thread_wrapper->allocator, join_thread_wrapper);

        aws_thread_decrement_unjoined_count();
    }
}

static DWORD WINAPI thread_wrapper_fn(LPVOID arg) {
    struct thread_wrapper *wrapper_ptr = arg;

    /*
     * Make sure the aws_thread copy has the right handle stored in it.
     * We can't just call GetCurrentThread since that returns a fake handle that always maps to the local thread which
     * isn't what we want.
     */
    DWORD current_thread_id = GetCurrentThreadId();
    wrapper_ptr->thread_copy.thread_handle = OpenThread(THREAD_ALL_ACCESS, FALSE, current_thread_id);

    struct thread_wrapper thread_wrapper = *wrapper_ptr;
    struct aws_allocator *allocator = thread_wrapper.allocator;
    tl_wrapper = &thread_wrapper;
    thread_wrapper.func(thread_wrapper.arg);

    /*
     * Managed threads don't free the wrapper yet.  The thread management system does it later after the thread
     * is joined.
     */
    bool is_managed_thread = wrapper_ptr->thread_copy.detach_state == AWS_THREAD_MANAGED;
    if (!is_managed_thread) {
        aws_mem_release(allocator, arg);
    }

    struct thread_atexit_callback *exit_callback_data = thread_wrapper.atexit;
    while (exit_callback_data) {
        aws_thread_atexit_fn *exit_callback = exit_callback_data->callback;
        void *exit_callback_user_data = exit_callback_data->user_data;
        struct thread_atexit_callback *next_exit_callback_data = exit_callback_data->next;

        aws_mem_release(allocator, exit_callback_data);

        exit_callback(exit_callback_user_data);
        exit_callback_data = next_exit_callback_data;
    }
    tl_wrapper = NULL;

    /*
     * Release this thread to the managed thread system for lazy join.
     */
    if (is_managed_thread) {
        aws_thread_pending_join_add(&wrapper_ptr->node);
    }

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

/* Check for functions that don't exist on ancient windows */
static aws_thread_once s_check_functions_once = INIT_ONCE_STATIC_INIT;

#if defined(AWS_OS_WINDOWS_DESKTOP)
static aws_thread_once s_check_active_processor_functions_once = INIT_ONCE_STATIC_INIT;
typedef DWORD WINAPI GetActiveProcessorCount_fn(WORD);
static GetActiveProcessorCount_fn *s_GetActiveProcessorCount;

typedef WORD WINAPI GetActiveProcessorGroupCount_fn(void);
static GetActiveProcessorGroupCount_fn *s_GetActiveProcessorGroupCount;

static void s_check_active_processor_functions(void *user_data) {
    (void)user_data;

    s_GetActiveProcessorGroupCount = (GetActiveProcessorGroupCount_fn *)GetProcAddress(
        GetModuleHandleW(WIDEN(WINDOWS_KERNEL_LIB) L".dll"), "GetActiveProcessorGroupCount");
    s_GetActiveProcessorCount = (GetActiveProcessorCount_fn *)GetProcAddress(
        GetModuleHandleW(WIDEN(WINDOWS_KERNEL_LIB) L".dll"), "GetActiveProcessorCount");
}
#endif

/* windows is weird because apparently no one ever considered computers having more than 64 processors. Instead they
   have processor groups per process. We need to find the mask in the correct group. */
static void s_get_group_and_cpu_id(uint32_t desired_cpu, uint16_t *group, uint8_t *proc_num) {
    (void)desired_cpu;
    *group = 0;
    *proc_num = 0;
#if defined(AWS_OS_WINDOWS_DESKTOP)
    /* Check for functions that don't exist on ancient Windows */
    aws_thread_call_once(&s_check_active_processor_functions_once, s_check_active_processor_functions, NULL);
    if (!s_GetActiveProcessorCount || !s_GetActiveProcessorGroupCount) {
        return;
    }

    unsigned group_count = s_GetActiveProcessorGroupCount();

    unsigned total_processors_detected = 0;
    uint8_t group_with_desired_processor = 0;
    uint8_t group_mask_for_desired_processor = 0;

    /* for each group, keep counting til we find the group and the processor mask */
    for (uint8_t i = 0; i < group_count; ++group_count) {
        DWORD processor_count_in_group = s_GetActiveProcessorCount((WORD)i);
        if (total_processors_detected + processor_count_in_group > desired_cpu) {
            group_with_desired_processor = i;
            group_mask_for_desired_processor = (uint8_t)(desired_cpu - total_processors_detected);
            break;
        }
        total_processors_detected += processor_count_in_group;
    }

    *proc_num = group_mask_for_desired_processor;
    *group = group_with_desired_processor;
    return;
#endif /* non-desktop has no processor groups */
}

typedef BOOL WINAPI SetThreadGroupAffinity_fn(
    HANDLE hThread,
    const GROUP_AFFINITY *GroupAffinity,
    PGROUP_AFFINITY PreviousGroupAffinity);
static SetThreadGroupAffinity_fn *s_SetThreadGroupAffinity;

typedef BOOL WINAPI SetThreadIdealProcessorEx_fn(
    HANDLE hThread,
    PPROCESSOR_NUMBER lpIdealProcessor,
    PPROCESSOR_NUMBER lpPreviousIdealProcessor);
static SetThreadIdealProcessorEx_fn *s_SetThreadIdealProcessorEx;

typedef HRESULT WINAPI SetThreadDescription_fn(HANDLE hThread, PCWSTR lpThreadDescription);
static SetThreadDescription_fn *s_SetThreadDescription;

typedef HRESULT WINAPI GetThreadDescription_fn(HANDLE hThread, PWSTR *lpThreadDescription);
static GetThreadDescription_fn *s_GetThreadDescription;

static void s_check_thread_functions(void *user_data) {
    (void)user_data;

    s_SetThreadGroupAffinity = (SetThreadGroupAffinity_fn *)GetProcAddress(
        GetModuleHandleW(WIDEN(WINDOWS_KERNEL_LIB) L".dll"), "SetThreadGroupAffinity");
    s_SetThreadIdealProcessorEx = (SetThreadIdealProcessorEx_fn *)GetProcAddress(
        GetModuleHandleW(WIDEN(WINDOWS_KERNEL_LIB) L".dll"), "SetThreadIdealProcessorEx");
    s_SetThreadDescription = (SetThreadDescription_fn *)GetProcAddress(
        GetModuleHandleW(WIDEN(WINDOWS_KERNEL_LIB) L".dll"), "SetThreadDescription");
    s_GetThreadDescription = (GetThreadDescription_fn *)GetProcAddress(
        GetModuleHandleW(WIDEN(WINDOWS_KERNEL_LIB) L".dll"), "GetThreadDescription");
}

int aws_thread_launch(
    struct aws_thread *thread,
    void (*func)(void *arg),
    void *arg,
    const struct aws_thread_options *options) {

    /* Check for functions that don't exist on ancient Windows */
    aws_thread_call_once(&s_check_functions_once, s_check_thread_functions, NULL);

    SIZE_T stack_size = 0;
    if (options && options->stack_size > 0) {
        stack_size = (SIZE_T)options->stack_size;
    }

    bool is_managed_thread = options != NULL && options->join_strategy == AWS_TJS_MANAGED;
    if (is_managed_thread) {
        thread->detach_state = AWS_THREAD_MANAGED;
    }

    struct thread_wrapper *thread_wrapper =
        (struct thread_wrapper *)aws_mem_calloc(thread->allocator, 1, sizeof(struct thread_wrapper));
    thread_wrapper->allocator = thread->allocator;
    thread_wrapper->arg = arg;
    thread_wrapper->func = func;
    thread_wrapper->thread_copy = *thread;

    /*
     * Increment the count prior to spawning the thread.  Decrement back if the create failed.
     */
    if (is_managed_thread) {
        aws_thread_increment_unjoined_count();
    }

    thread->thread_handle =
        CreateThread(0, stack_size, thread_wrapper_fn, (LPVOID)thread_wrapper, 0, &thread->thread_id);

    if (!thread->thread_handle) {
        aws_thread_decrement_unjoined_count();
        return aws_raise_error(AWS_ERROR_THREAD_INSUFFICIENT_RESOURCE);
    }

    if (options && (options->name.len > 0) && s_SetThreadDescription) {
        /* Don't particularly care if this fails, it's just for debugging */
        struct aws_wstring *name = aws_string_convert_to_wchar_from_byte_cursor(thread->allocator, &options->name);
        if (name) {
            s_SetThreadDescription(thread->thread_handle, aws_wstring_c_str(name));
            aws_wstring_destroy(name);
        }
    }

    if (options && options->cpu_id >= 0) {
        AWS_LOGF_INFO(
            AWS_LS_COMMON_THREAD,
            "id=%p: cpu affinity of cpu_id %" PRIi32 " was specified, attempting to honor the value.",
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
            "id=%p: computed mask %" PRIx64 " on group %" PRIu16 ".",
            (void *)thread,
            (uint64_t)group_afinity.Mask,
            (uint16_t)group_afinity.Group);

        if (!s_SetThreadGroupAffinity || !s_SetThreadIdealProcessorEx) {
            goto no_thread_affinity;
        }
        BOOL set_group_val = s_SetThreadGroupAffinity(thread->thread_handle, &group_afinity, NULL);
        AWS_LOGF_DEBUG(
            AWS_LS_COMMON_THREAD,
            "id=%p: SetThreadGroupAffinity() result %" PRIi8 ".",
            (void *)thread,
            (int8_t)set_group_val);

        if (set_group_val) {
            PROCESSOR_NUMBER processor_number;
            AWS_ZERO_STRUCT(processor_number);
            processor_number.Group = (WORD)group;
            processor_number.Number = proc_num;

            BOOL set_processor_val = s_SetThreadIdealProcessorEx(thread->thread_handle, &processor_number, NULL);
            AWS_LOGF_DEBUG(
                AWS_LS_COMMON_THREAD,
                "id=%p: SetThreadIdealProcessorEx() result %" PRIi8 ".",
                (void *)thread,
                (int8_t)set_processor_val);
            if (!set_processor_val) {
                AWS_LOGF_WARN(
                    AWS_LS_COMMON_THREAD,
                    "id=%p: SetThreadIdealProcessorEx() failed with %" PRIx32 ".",
                    (void *)thread,
                    (uint32_t)GetLastError());
            }

        } else {
            AWS_LOGF_WARN(
                AWS_LS_COMMON_THREAD,
                "id=%p: SetThreadGroupAffinity() failed with %" PRIx32 ".",
                (void *)thread,
                (uint32_t)GetLastError());
        }
    }
no_thread_affinity:
    /*
     * Managed threads need to stay unjoinable from an external perspective.  We'll handle it after thread function
     * completion.
     */
    if (is_managed_thread) {
        aws_thread_clean_up(thread);
    } else {
        thread->detach_state = AWS_THREAD_JOINABLE;
    }

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

int aws_thread_current_name(struct aws_allocator *allocator, struct aws_string **out_name) {
    if (s_GetThreadDescription) {

        PWSTR wname = NULL;
        if (SUCCEEDED(s_GetThreadDescription(GetCurrentThread(), &wname))) {
            *out_name = aws_string_convert_from_wchar_c_str(allocator, wname);
            LocalFree(wname);
            return AWS_OP_SUCCESS;
        }

        return aws_raise_error(AWS_ERROR_SYS_CALL_FAILURE);
    }

    return aws_raise_error(AWS_ERROR_PLATFORM_NOT_SUPPORTED);
}

int aws_thread_name(struct aws_allocator *allocator, aws_thread_id_t thread_id, struct aws_string **out_name) {
    if (s_GetThreadDescription) {

        HANDLE thread_handle = OpenThread(THREAD_QUERY_LIMITED_INFORMATION, FALSE, thread_id);

        if (thread_handle == NULL) {
            AWS_LOGF_WARN(
                AWS_LS_COMMON_THREAD,
                "thread_id=%lu: OpenThread() failed with %" PRIx32 ".",
                thread_id,
                (uint32_t)GetLastError());
            return aws_raise_error(AWS_ERROR_SYS_CALL_FAILURE);
        }

        PWSTR wname = NULL;
        if (SUCCEEDED(s_GetThreadDescription(thread_handle, &wname))) {
            *out_name = aws_string_convert_from_wchar_c_str(allocator, wname);
            LocalFree(wname);
            CloseHandle(thread_handle);
            return AWS_OP_SUCCESS;
        }

        CloseHandle(thread_handle);
        return aws_raise_error(AWS_ERROR_SYS_CALL_FAILURE);
    }

    return aws_raise_error(AWS_ERROR_PLATFORM_NOT_SUPPORTED);
}
