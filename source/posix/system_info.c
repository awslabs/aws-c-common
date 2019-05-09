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

#include <aws/common/assert.h>

#if defined(__FreeBSD__) || defined(__NetBSD__)
#    define __BSD_VISIBLE 1
#endif

#include <unistd.h>

#if defined(HAVE_SYSCONF)
size_t aws_system_info_processor_count(void) {
    long nprocs = sysconf(_SC_NPROCESSORS_ONLN);
    if (AWS_LIKELY(nprocs >= 0)) {
        return (size_t)nprocs;
    }

    AWS_FATAL_ASSERT(nprocs >= 0);
    return 0;
}
#else
size_t aws_system_info_processor_count(void) {
#    if defined(AWS_NUM_CPU_CORES)
    AWS_FATAL_ASSERT(AWS_NUM_CPU_CORES > 0);
    return AWS_NUM_CPU_CORES;
#    else
    return 1;
#    endif
}
#endif

#include <signal.h>

void aws_debug_break(void)
{
#if defined(__clang__) && __has_builtin(__builtin_debugtrap)
    __builtin_debugtrap();
#else
    raise(SIGTRAP);
#endif
}

#if defined(AWS_HAS_EXECINFO)
#include <execinfo.h>
#include <limits.h>

#define AWS_BACKTRACE_DEPTH 128

void aws_backtrace_print(FILE *fp, void *call_site_data)
{
    siginfo_t *siginfo = call_site_data;
    if (siginfo) {
        fprintf(fp, "Signal received: %d, errno: %d\n", siginfo->si_signo, siginfo->si_errno);
        if (siginfo->si_signo == SIGSEGV) {
            fprintf(fp, "  SIGSEGV @ 0x%p\n", siginfo->si_addr);
        }
    }

    void *stack_frames[AWS_BACKTRACE_DEPTH];
    int stack_depth = backtrace(stack_frames, AWS_BACKTRACE_DEPTH);
    char **symbols = backtrace_symbols(stack_frames, stack_depth);
    if (symbols == NULL)
    {
        fprintf(fp, "Unable to decode backtrace via backtrace_symbols\n");
        return;
    }

    /* symbols look like: <exe-or-shared-lib>(<function>) [0x<addr>] */
    /* start at 1 to skip the current frame (this function) */
    for (int frame_idx = 1; frame_idx < stack_depth; ++frame_idx) {
        const char *frame_info = symbols[frame_idx];
        long open_paren_pos = strstr(symbols[frame_idx], "(") - symbols[frame_idx];
        long close_paren_pos = strstr(symbols[frame_idx] + open_paren_pos, ")") - symbols[frame_idx];
        if (open_paren_pos <= 0 || close_paren_pos < 0) {
            goto unresolved;
        }

        char exe[PATH_MAX] = {0};
        strncpy(exe, symbols[frame_idx], open_paren_pos);
        exe[open_paren_pos] = 0;

        long function_len = close_paren_pos - (open_paren_pos + 1);
        if (function_len) { /* dynamic symbol was found */
            goto unresolved;
        }

        const char *addr_start = strstr(symbols[frame_idx], "[") + 1;
        char *addr_end = strstr(addr_start, "]");
        if (!addr_end) {
            goto unresolved;
        }
        *addr_end = 0;

        /* TODO: Emulate libunwind */
        char cmd[1024] = {0};
        snprintf(cmd, 1024, "addr2line -afips -e %s %s", exe, addr_start);
        FILE *out = popen(cmd, "r");
        if (!out) {
            goto unresolved;
        }
        char output[1024];
        fgets(output, sizeof(output), out);
        pclose(out);
        frame_info = output;

    unresolved:
        fprintf(fp, "%s%s", frame_info, (frame_info == symbols[frame_idx]) ? "\n" : "");
    }
    free(symbols);
}

#else
void aws_backtrace_print(FILE *fp, void *call_site_data) {
    fprintf(fp, "No call stack information available\n");
}
#endif /* AWS_HAS_EXECINFO */
