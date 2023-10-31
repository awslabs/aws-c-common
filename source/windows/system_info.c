/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */
#include <aws/common/private/system_info_priv.h>

#include <aws/common/byte_buf.h>
#include <aws/common/logging.h>
#include <aws/common/thread.h>

#include <Windows.h>

enum aws_platform_os aws_get_platform_build_os(void) {
    return AWS_PLATFORM_OS_WINDOWS;
}

size_t aws_system_info_processor_count(void) {
    SYSTEM_INFO info;
    GetSystemInfo(&info);
    return info.dwNumberOfProcessors;
}


#if defined(AWS_OS_WINDOWS_DESKTOP)
/* Convert a string from a macro to a wide string */
#    define WIDEN2(s) L## #    s
#    define WIDEN(s) WIDEN2(s)

static aws_thread_once s_check_active_processor_functions_once = INIT_ONCE_STATIC_INIT;

typedef BOOL WINAPI GetLogicalProcessorInformationEx_fn(
    LOGICAL_PROCESSOR_RELATIONSHIP RelationshipType,
    PSYSTEM_LOGICAL_PROCESSOR_INFORMATION_EX Buffer,
    PDWORD ReturnedLength);
static GetLogicalProcessorInformationEx_fn *s_GetLogicalProcessorInformationEx;


static void s_check_active_processor_functions(void *user_data) {
    (void)user_data;

    s_GetLogicalProcessorInformationEx =
        (GetLogicalProcessorInformationEx_fn *)GetProcAddress(GetModuleHandleW(WIDEN(WINDOWS_KERNEL_LIB) L".dll"),
         "GetLogicalProcessorInformationEx");

}
#endif

uint16_t aws_get_cpu_group_count(void) {
#if defined(AWS_OS_WINDOWS_DESKTOP)
    /* Check for functions that don't exist on ancient Windows */
    aws_thread_call_once(&s_check_active_processor_functions_once, s_check_active_processor_functions, NULL);
    AWS_FATAL_ASSERT(s_GetLogicalProcessorInformationEx);

    ULONG buffer_length = 0;
    s_GetLogicalProcessorInformationEx(RelationNumaNode, NULL, &buffer_length);
    AWS_FATAL_ASSERT(buffer_length);

    struct aws_allocator *allocator = aws_default_allocator();
    PSYSTEM_LOGICAL_PROCESSOR_INFORMATION_EX buffer =
        (PSYSTEM_LOGICAL_PROCESSOR_INFORMATION_EX)aws_mem_acquire(allocator, buffer_length);
    AWS_FATAL_ASSERT(s_GetLogicalProcessorInformationEx(RelationNumaNode, buffer, &buffer_length));

    uint16_t count = 0;
    ULONG offset = 0;
    while (offset < buffer_length) {
        PSYSTEM_LOGICAL_PROCESSOR_INFORMATION_EX info =
            (PSYSTEM_LOGICAL_PROCESSOR_INFORMATION_EX)((uint8_t *)buffer + offset);
        if (info->Relationship == RelationNumaNode) {
            count++;
        }
        offset += info->Size;
    }

    aws_mem_release(allocator, buffer);
    return count;
#else
    return 1L;
#endif /* defined(AWS_OS_WINDOWS_DESKTOP) */
}

static size_t s_count_set_bits(ULONGLONG number) {
    size_t count = 0;
    while (number) {
        count += number & 1;
        number >>= 1;
    }
    return count;
}

size_t aws_get_cpu_count_for_group(uint16_t group_idx) {

#if defined(AWS_OS_WINDOWS_DESKTOP)
    aws_thread_call_once(&s_check_active_processor_functions_once, s_check_active_processor_functions, NULL);
    AWS_FATAL_ASSERT(s_GetLogicalProcessorInformationEx);
    ULONG buffer_length = 0;
    s_GetLogicalProcessorInformationEx(RelationNumaNode, NULL, &buffer_length);
    AWS_FATAL_ASSERT(buffer_length);

    struct aws_allocator *allocator = aws_default_allocator();
    PSYSTEM_LOGICAL_PROCESSOR_INFORMATION_EX buffer =
        (PSYSTEM_LOGICAL_PROCESSOR_INFORMATION_EX)aws_mem_acquire(allocator, buffer_length);
    AWS_FATAL_ASSERT(s_GetLogicalProcessorInformationEx(RelationNumaNode, buffer, &buffer_length));

    size_t cpu_count = 0;
    ULONG offset = 0;
    while (offset < buffer_length) {
        PSYSTEM_LOGICAL_PROCESSOR_INFORMATION_EX info =
            (PSYSTEM_LOGICAL_PROCESSOR_INFORMATION_EX)((uint8_t *)buffer + offset);
        if (info->Relationship == RelationNumaNode && info->NumaNode.NodeNumber == group_idx) {
            cpu_count = s_count_set_bits(info->NumaNode.GroupMask.Mask);
            break;
        }
        offset += info->Size;
    }

    aws_mem_release(allocator, buffer);
    return cpu_count;
#else
    return group_idx == 0 ? aws_system_info_processor_count() : 0;
#endif /* defined(AWS_OS_WINDOWS_DESKTOP) */

}

void aws_get_cpu_ids_for_group(uint16_t group_idx, struct aws_cpu_info *cpu_ids_array, size_t cpu_ids_array_length) {
#if defined(AWS_OS_WINDOWS_DESKTOP)
    /* Check for functions that don't exist on ancient Windows */
    aws_thread_call_once(&s_check_active_processor_functions_once, s_check_active_processor_functions, NULL);
    AWS_FATAL_ASSERT(s_GetLogicalProcessorInformationEx);

    ULONG buffer_length = 0;
    s_GetLogicalProcessorInformationEx(RelationNumaNode, NULL, &buffer_length);
    AWS_FATAL_ASSERT(buffer_length);

    struct aws_allocator *allocator = aws_default_allocator();
    PSYSTEM_LOGICAL_PROCESSOR_INFORMATION_EX buffer =
        (PSYSTEM_LOGICAL_PROCESSOR_INFORMATION_EX)aws_mem_acquire(allocator, buffer_length);
    AWS_FATAL_ASSERT(s_GetLogicalProcessorInformationEx(RelationNumaNode, buffer, &buffer_length));

    size_t cpu_count = 0;
    ULONG offset = 0;
    size_t hyper_threads_hint = cpu_ids_array_length / 2 - 1;

    while (offset < buffer_length) {
        PSYSTEM_LOGICAL_PROCESSOR_INFORMATION_EX info =
            (PSYSTEM_LOGICAL_PROCESSOR_INFORMATION_EX)((uint8_t *)buffer + offset);
        if (info->Relationship == RelationNumaNode && info->NumaNode.NodeNumber == group_idx) {
            ULONGLONG mask = info->NumaNode.GroupMask.Mask;
            for (size_t i = 0; i < cpu_ids_array_length; i++) {
                if (mask & ((ULONGLONG)1 << i)) {
                    cpu_ids_array[i].cpu_id = (int32_t)i;
                    cpu_ids_array[i].suspected_hyper_thread = i > hyper_threads_hint;
                }
            }
            break;
        }
        offset += info->Size;
    }

    aws_mem_release(allocator, buffer);
#else
    /* a crude hint, but hyper-threads are numbered as the second half of the cpu id listing. */
    size_t hyper_threads_hint = cpu_ids_array_length / 2 - 1;

    for (size_t i = 0; i < cpu_ids_array_length; ++i) {
        cpu_ids_array[i].cpu_id = (int32_t)i;
        cpu_ids_array[i].suspected_hyper_thread = i > hyper_threads_hint;
    }
#endif /* defined(AWS_OS_WINDOWS_DESKTOP) */
}

bool aws_is_debugger_present(void) {
    return IsDebuggerPresent();
}

void aws_debug_break(void) {
#ifdef DEBUG_BUILD
    if (aws_is_debugger_present()) {
        DebugBreak();
    }
#endif
}

#if defined(AWS_OS_WINDOWS_DESKTOP)

/* If I meet the engineer that wrote the dbghelp.h file for the windows 8.1 SDK we're gonna have words! */
#    ifdef _MSC_VER
#        pragma warning(disable : 4091)
#    endif
#    include <dbghelp.h>

struct win_symbol_data {
    struct _SYMBOL_INFO sym_info;
    char symbol_name[1024];
};

typedef BOOL __stdcall SymInitialize_fn(_In_ HANDLE hProcess, _In_opt_ PCSTR UserSearchPath, _In_ BOOL fInvadeProcess);
typedef DWORD __stdcall SymSetOptions_fn(DWORD SymOptions);

typedef BOOL __stdcall SymFromAddr_fn(
    _In_ HANDLE hProcess,
    _In_ DWORD64 Address,
    _Out_opt_ PDWORD64 Displacement,
    _Inout_ PSYMBOL_INFO Symbol);

#    if defined(_WIN64)
typedef BOOL __stdcall SymGetLineFromAddr_fn(
    _In_ HANDLE hProcess,
    _In_ DWORD64 qwAddr,
    _Out_ PDWORD pdwDisplacement,
    _Out_ PIMAGEHLP_LINE64 Line64);
#        define SymGetLineFromAddrName "SymGetLineFromAddr64"
#    else
typedef BOOL __stdcall SymGetLineFromAddr_fn(
    _In_ HANDLE hProcess,
    _In_ DWORD dwAddr,
    _Out_ PDWORD pdwDisplacement,
    _Out_ PIMAGEHLP_LINE Line);
#        define SymGetLineFromAddrName "SymGetLineFromAddr"
#    endif

static SymInitialize_fn *s_SymInitialize = NULL;
static SymSetOptions_fn *s_SymSetOptions = NULL;
static SymFromAddr_fn *s_SymFromAddr = NULL;
static SymGetLineFromAddr_fn *s_SymGetLineFromAddr = NULL;

static aws_thread_once s_init_once = AWS_THREAD_ONCE_STATIC_INIT;
static void s_init_dbghelp_impl(void *user_data) {
    (void)user_data;
    HMODULE dbghelp = LoadLibraryA("DbgHelp.dll");
    if (!dbghelp) {
        fprintf(stderr, "Failed to load DbgHelp.dll.\n");
        goto done;
    }

    s_SymInitialize = (SymInitialize_fn *)GetProcAddress(dbghelp, "SymInitialize");
    if (!s_SymInitialize) {
        fprintf(stderr, "Failed to load SymInitialize from DbgHelp.dll.\n");
        goto done;
    }

    s_SymSetOptions = (SymSetOptions_fn *)GetProcAddress(dbghelp, "SymSetOptions");
    if (!s_SymSetOptions) {
        fprintf(stderr, "Failed to load SymSetOptions from DbgHelp.dll\n");
        goto done;
    }

    s_SymFromAddr = (SymFromAddr_fn *)GetProcAddress(dbghelp, "SymFromAddr");
    if (!s_SymFromAddr) {
        fprintf(stderr, "Failed to load SymFromAddr from DbgHelp.dll.\n");
        goto done;
    }

    s_SymGetLineFromAddr = (SymGetLineFromAddr_fn *)GetProcAddress(dbghelp, SymGetLineFromAddrName);
    if (!s_SymGetLineFromAddr) {
        fprintf(stderr, "Failed to load " SymGetLineFromAddrName " from DbgHelp.dll.\n");
        goto done;
    }

    HANDLE process = GetCurrentProcess();
    AWS_FATAL_ASSERT(process);
    s_SymInitialize(process, NULL, TRUE);
    s_SymSetOptions(SYMOPT_DEFERRED_LOADS | SYMOPT_LOAD_ANYTHING | SYMOPT_LOAD_LINES);
    return;

done:
    if (dbghelp) {
        FreeLibrary(dbghelp);
    }
    return;
}

static bool s_init_dbghelp() {
    if (AWS_LIKELY(s_SymInitialize)) {
        return true;
    }

    aws_thread_call_once(&s_init_once, s_init_dbghelp_impl, NULL);
    return s_SymInitialize != NULL;
}

size_t aws_backtrace(void **stack_frames, size_t num_frames) {
    return (int)CaptureStackBackTrace(0, (ULONG)num_frames, stack_frames, NULL);
}

char **aws_backtrace_symbols(void *const *stack_frames, size_t num_frames) {
    if (!s_init_dbghelp()) {
        return NULL;
    }

    struct aws_byte_buf symbols;
    aws_byte_buf_init(&symbols, aws_default_allocator(), num_frames * 256);
    /* pointers for each stack entry */
    memset(symbols.buffer, 0, num_frames * sizeof(void *));
    symbols.len += num_frames * sizeof(void *);

    DWORD64 displacement = 0;
    DWORD disp = 0;

    struct aws_byte_cursor null_term = aws_byte_cursor_from_array("", 1);
    HANDLE process = GetCurrentProcess();
    AWS_FATAL_ASSERT(process);
    for (size_t i = 0; i < num_frames; ++i) {
        /* record a pointer to where the symbol will be */
        *((char **)&symbols.buffer[i * sizeof(void *)]) = (char *)symbols.buffer + symbols.len;

        uintptr_t address = (uintptr_t)stack_frames[i];
        struct win_symbol_data sym_info;
        AWS_ZERO_STRUCT(sym_info);
        sym_info.sym_info.MaxNameLen = sizeof(sym_info.symbol_name);
        sym_info.sym_info.SizeOfStruct = sizeof(struct _SYMBOL_INFO);

        char sym_buf[1024]; /* scratch space for extracting info */
        if (s_SymFromAddr(process, address, &displacement, &sym_info.sym_info)) {
            /* record the address and name */
            int len = snprintf(
                sym_buf, AWS_ARRAY_SIZE(sym_buf), "at 0x%llX: %s", sym_info.sym_info.Address, sym_info.sym_info.Name);
            if (len != -1) {
                struct aws_byte_cursor symbol = aws_byte_cursor_from_array(sym_buf, len);
                aws_byte_buf_append_dynamic(&symbols, &symbol);
            }

            IMAGEHLP_LINE line;
            line.SizeOfStruct = sizeof(IMAGEHLP_LINE);
            if (s_SymGetLineFromAddr(process, address, &disp, &line)) {
                /* record file/line info */
                len = snprintf(sym_buf, AWS_ARRAY_SIZE(sym_buf), "(%s:%lu)", line.FileName, line.LineNumber);
                if (len != -1) {
                    struct aws_byte_cursor symbol = aws_byte_cursor_from_array(sym_buf, len);
                    aws_byte_buf_append_dynamic(&symbols, &symbol);
                }
            }
        } else {
            /* no luck, record the address and last error */
            DWORD last_error = GetLastError();
            int len = snprintf(
                sym_buf,
                AWS_ARRAY_SIZE(sym_buf),
                "at 0x%p: Failed to lookup symbol: error %u",
                stack_frames[i],
                last_error);
            if (len > 0) {
                struct aws_byte_cursor sym_cur = aws_byte_cursor_from_array(sym_buf, len);
                aws_byte_buf_append_dynamic(&symbols, &sym_cur);
            }
        }

        /* Null terminator */
        aws_byte_buf_append_dynamic(&symbols, &null_term);
    }

    return (char **)symbols.buffer; /* buffer must be freed by the caller */
}

char **aws_backtrace_addr2line(void *const *stack_frames, size_t stack_depth) {
    return aws_backtrace_symbols(stack_frames, stack_depth);
}

void aws_backtrace_print(FILE *fp, void *call_site_data) {
    struct _EXCEPTION_POINTERS *exception_pointers = call_site_data;
    if (exception_pointers) {
        fprintf(fp, "** Exception 0x%x occured **\n", exception_pointers->ExceptionRecord->ExceptionCode);
    }

    if (!s_init_dbghelp()) {
        fprintf(fp, "Unable to initialize dbghelp.dll");
        return;
    }

    void *stack[1024];
    size_t num_frames = aws_backtrace(stack, 1024);
    char **symbols = aws_backtrace_symbols(stack, num_frames);
    for (size_t line = 0; line < num_frames; ++line) {
        const char *symbol = symbols[line];
        fprintf(fp, "%s\n", symbol);
    }
    fflush(fp);
    aws_mem_release(aws_default_allocator(), symbols);
}

void aws_backtrace_log(int log_level) {
    if (!s_init_dbghelp()) {
        AWS_LOGF_ERROR(AWS_LS_COMMON_GENERAL, "Unable to initialize dbghelp.dll for backtrace");
        return;
    }

    void *stack[1024];
    size_t num_frames = aws_backtrace(stack, 1024);
    char **symbols = aws_backtrace_symbols(stack, num_frames);
    for (size_t line = 0; line < num_frames; ++line) {
        const char *symbol = symbols[line];
        AWS_LOGF(log_level, AWS_LS_COMMON_GENERAL, "%s", symbol);
    }
    aws_mem_release(aws_default_allocator(), symbols);
}
#else /* !AWS_OS_WINDOWS_DESKTOP */
size_t aws_backtrace(void **stack_frames, size_t num_frames) {
    (void)stack_frames;
    (void)num_frames;
    return 0;
}
char **aws_backtrace_symbols(void *const *stack_frames, size_t stack_depth) {
    (void)stack_frames;
    (void)stack_depth;
    return NULL;
}

char **aws_backtrace_addr2line(void *const *stack_frames, size_t stack_depth) {
    return aws_backtrace_symbols(stack_frames, stack_depth);
}

void aws_backtrace_print(FILE *fp, void *call_site_data) {
    (void)fp;
    (void)call_site_data;
    AWS_LOGF_TRACE(
        AWS_LS_COMMON_GENERAL, "aws_backtrace_print: backtrace requested, but logging is unsupported on this platform");
}

void aws_backtrace_log() {
    AWS_LOGF_TRACE(
        AWS_LS_COMMON_GENERAL, "aws_backtrace_log: backtrace requested, but logging is unsupported on this platform");
}

#endif /* AWS_OS_WINDOWS_DESKTOP */
