# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0.

include(CheckSymbolExists)

# Check how the platform supports setting thread name
function(aws_set_thread_name_method target)

    function(aws_set_thread_name_setter_method target)
        if (APPLE)
            # All Apple platforms we support have 1 arg version of the function.
            # So skip compile time check here and instead check if its apple in
            # the thread code.
            return()
        endif()

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

        # OpenBSD's function takes 2 args, but has a different name.
        check_c_source_compiles("
            ${c_source_start}
            pthread_set_name_np(thread_id, \"asdf\");
            ${c_source_end}"
            PTHREAD_SET_NAME_TAKES_2ARGS)
        if (PTHREAD_SET_NAME_TAKES_2ARGS)
            target_compile_definitions(${target} PRIVATE -DAWS_PTHREAD_SET_NAME_TAKES_2ARGS)
            return()
        endif()

        # But on NetBSD it takes 3!
        check_c_source_compiles("
            ${c_source_start}
            pthread_setname_np(thread_id, \"asdf\", NULL);
            ${c_source_end}
            " PTHREAD_SETNAME_TAKES_3ARGS)
        if (PTHREAD_SETNAME_TAKES_3ARGS)
            target_compile_definitions(${target} PRIVATE -DAWS_PTHREAD_SETNAME_TAKES_3ARGS)
            return()
        endif()

        # And on many older/weirder platforms it's just not supported
        # Consider using prctl if we really want to support those
    endfunction()

    function(aws_set_thread_name_getter_method target)
        if (APPLE)
            # All Apple platforms we support have the same function, so no need for
            # compile-time check.
            target_compile_definitions(${target} PRIVATE -DAWS_PTHREAD_GETNAME_TAKES_3ARGS)
            return()
        endif()

        # Some platforms have 2 arg version
        check_c_source_compiles("
            ${c_source_start}
                char name[16] = {0};
                pthread_getname_np(thread_id, name);
            ${c_source_end}
        " PTHREAD_GETNAME_TAKES_2ARGS)
        if (PTHREAD_GETNAME_TAKES_2ARGS)
            target_compile_definitions(${target} PRIVATE -DAWS_PTHREAD_GETNAME_TAKES_2ARGS)
            return()
        endif()

        # Some platforms have 2 arg version but with a different name (eg, OpenBSD)
        check_c_source_compiles("
            ${c_source_start}
                char name[16] = {0};
                pthread_get_name_np(thread_id, name);
            ${c_source_end}
        " PTHREAD_GET_NAME_TAKES_2ARGS)
        if (PTHREAD_GET_NAME_TAKES_2ARGS)
            target_compile_definitions(${target} PRIVATE -DAWS_PTHREAD_GET_NAME_TAKES_2ARGS)
            return()
        endif()

        # But majority have 3
        check_c_source_compiles("
            ${c_source_start}
                char name[16] = {0};
                pthread_getname_np(thread_id, name, 16);
            ${c_source_end}
        " PTHREAD_GETNAME_TAKES_3ARGS)
        if (PTHREAD_GETNAME_TAKES_3ARGS)
            target_compile_definitions(${target} PRIVATE -DAWS_PTHREAD_GETNAME_TAKES_3ARGS)
            return()
        endif()

    endfunction()

    if (WIN32)
        # On Windows we do a runtime check for both getter and setter, instead of compile-time check
        return()
    endif()

    list(APPEND CMAKE_REQUIRED_DEFINITIONS -D_GNU_SOURCE)
    list(APPEND CMAKE_REQUIRED_LIBRARIES pthread)

    # The start of the test program
    set(c_source_start "
        #define _GNU_SOURCE
        #include <pthread.h>

        #if defined(__FreeBSD__) || defined(__NetBSD__) || defined(__OpenBSD__)
        #include <pthread_np.h>
        #endif

        int main() {
            pthread_t thread_id;
        ")

    # The end of the test program
    set(c_source_end "}")

    aws_set_thread_name_setter_method(${target})
    aws_set_thread_name_getter_method(${target})
endfunction()
