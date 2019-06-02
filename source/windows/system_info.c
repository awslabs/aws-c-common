/*
 * Copyright 2010-2018 Amazon.com, Inc. or its affiliates. All Rights Reserved.
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

#include <aws/common/system_info.h>

#include <windows.h>

size_t aws_system_info_processor_count(void) {
    SYSTEM_INFO info;
    GetSystemInfo(&info);
    return info.dwNumberOfProcessors;
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

/* If I meet the engineer that wrote the dbghelp.h file for the windows 8.1 SDK we're gonna have words! */
#pragma warning(disable : 4091)
#include <dbghelp.h>

struct win_symbol_data {
    struct _SYMBOL_INFO sym_info;
    char symbol_name[1024];
};

typedef BOOL __stdcall SymInitialize_fn(_In_ HANDLE hProcess, _In_opt_ PCSTR UserSearchPath, _In_ BOOL fInvadeProcess);

typedef BOOL __stdcall SymFromAddr_fn(
    _In_ HANDLE hProcess,
    _In_ DWORD64 Address,
    _Out_opt_ PDWORD64 Displacement,
    _Inout_ PSYMBOL_INFO Symbol);

#if defined(_WIN64)
typedef BOOL __stdcall SymGetLineFromAddr_fn(
    _In_ HANDLE hProcess,
    _In_ DWORD64 qwAddr,
    _Out_ PDWORD pdwDisplacement,
    _Out_ PIMAGEHLP_LINE64 Line64);
#    define SymGetLineFromAddrName "SymGetLineFromAddr64"
#else
typedef BOOL __stdcall SymGetLineFromAddr_fn(
    _In_ HANDLE hProcess,
    _In_ DWORD dwAddr,
    _Out_ PDWORD pdwDisplacement,
    _Out_ PIMAGEHLP_LINE Line);
#    define SymGetLineFromAddrName "SymGetLineFromAddr"
#endif

void aws_backtrace_print(FILE *fp, void *call_site_data) {
    struct _EXCEPTION_POINTERS *exception_pointers = call_site_data;
    if (exception_pointers) {
        fprintf(fp, "** Exception 0x%x occured **\n", exception_pointers->ExceptionRecord->ExceptionCode);
    }

    HMODULE dbghelp = LoadLibraryA("DbgHelp.dll");
    if (!dbghelp) {
        fprintf(stderr, "Failed to load DbgHelp.dll.\n");
        goto done;
    }

    SymInitialize_fn *p_SymInitialize = (SymInitialize_fn *)GetProcAddress(dbghelp, "SymInitialize");
    if (!p_SymInitialize) {
        fprintf(stderr, "Failed to load SymInitialize from DbgHelp.dll.\n");
        goto done;
    }

    SymFromAddr_fn *p_SymFromAddr = (SymFromAddr_fn *)GetProcAddress(dbghelp, "SymFromAddr");
    if (!p_SymFromAddr) {
        fprintf(stderr, "Failed to load SymFromAddr from DbgHelp.dll.\n");
        goto done;
    }

    SymGetLineFromAddr_fn *p_SymGetLineFromAddr =
        (SymGetLineFromAddr_fn *)GetProcAddress(dbghelp, SymGetLineFromAddrName);
    if (!p_SymGetLineFromAddr) {
        fprintf(stderr, "Failed to load " SymGetLineFromAddrName " from DbgHelp.dll.\n");
        goto done;
    }

    HANDLE process = GetCurrentProcess();
    p_SymInitialize(process, NULL, TRUE);
    void *stack[1024];
    WORD num_frames = CaptureStackBackTrace(0, 1024, stack, NULL);
    DWORD64 displacement = 0;
    DWORD disp = 0;

    fprintf(stderr, "Stack Trace:\n");
    for (size_t i = 0; i < num_frames; ++i) {
        uintptr_t address = (uintptr_t)stack[i];
        struct win_symbol_data sym_info;
        AWS_ZERO_STRUCT(sym_info);
        sym_info.sym_info.MaxNameLen = sizeof(sym_info.symbol_name);
        sym_info.sym_info.SizeOfStruct = sizeof(struct _SYMBOL_INFO);
        p_SymFromAddr(process, address, &displacement, &sym_info.sym_info);

        IMAGEHLP_LINE line;
        line.SizeOfStruct = sizeof(IMAGEHLP_LINE);
        if (p_SymGetLineFromAddr(process, address, &disp, &line)) {
            if (i != 0) {
                fprintf(
                    stderr,
                    "at %s(%s:%lu): address: 0x%llX\n",
                    sym_info.sym_info.Name,
                    line.FileName,
                    line.LineNumber,
                    sym_info.sym_info.Address);
            }
        }
    }

done:
    if (dbghelp) {
        FreeLibrary(dbghelp);
    }
}
