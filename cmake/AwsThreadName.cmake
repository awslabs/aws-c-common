# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0.

include(CheckSymbolExists)

# Check how the platform supports setting thread name
function(aws_set_thread_name_method target)

    if (WINDOWS)
        # On Windows we do a runtime check, instead of compile-time check
        return()
    elseif (APPLE)
        # All modern Apple OSs are the same, and we don't support ancient APPLE, so no need for compile-time check
        return()
    endif()

    list(APPEND CMAKE_REQUIRED_DEFINITIONS -D_GNU_SOURCE)
    list(APPEND CMAKE_REQUIRED_LIBRARIES pthread)

    set(c_source_start "
        #define _GNU_SOURCE
        #include <pthread.h>

        #if defined(__FreeBSD__) || defined(__NETBSD__)
        #include <pthread_np.h>
        #endif

        int main() {
            pthread_t thread_id;
        ")

    set(c_source_end "}")

    # pthread_setname_np() usually takes 2 args
    check_c_source_compiles("
        ${c_source_start}
        pthread_setname_np(thread_id, \"asdf\");
        ${c_source_end}"
        PTHREAD_SETNAME_TAKES_2ARGS)
    if (PTHREAD_SETNAME_TAKES_2ARGS)
        target_compile_definitions(${target} PRIVATE -DAWS_PTHREAD_SETNAME_TAKES_2ARGS)
        return()
    endif()

    # it takes 3 args on modern NetBSD
    check_c_source_compiles("
        ${c_source_start}
        pthread_setname_np(thread_id, \"asdf\", NULL);
        ${c_source_end}
        " PTHREAD_SETNAME_TAKES_3ARGS)
    if (PTHREAD_SETNAME_TAKES_3ARGS)
        target_compile_definitions(${target} PRIVATE -DAWS_PTHREAD_SETNAME_TAKES_3ARGS)
        return()
    endif()

    # And on older/weirder platforms it's just not supported
endfunction()
