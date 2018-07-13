# Copyright 2010-2018 Amazon.com, Inc. or its affiliates. All Rights Reserved.
#
# Licensed under the Apache License, Version 2.0 (the "License").
# You may not use this file except in compliance with the License.
# A copy of the License is located at
#
#  http://aws.amazon.com/apache2.0
#
# or in the "license" file accompanying this file. This file is distributed
# on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
# express or implied. See the License for the specific language governing
# permissions and limitations under the License.

include(CheckCCompilerFlag)

function(aws_add_sanitizers target)
    if(CMAKE_BUILD_TYPE STREQUAL "" OR CMAKE_BUILD_TYPE MATCHES Debug)
        check_c_compiler_flag(-fsanitize= HAS_SANITIZERS)
        if(HAS_SANITIZERS)
            if(ARGN)
                set(SANITIZERS ${ARGN})
            else()
                set(SANITIZERS "address;undefined")
            endif()

            foreach (sanitizer IN LISTS SANITIZERS)

                # When testing for libfuzzer, if attempting to link there will be 2 mains
                if(${sanitizer} STREQUAL "fuzzer")
                    set(sanitizer_test_flag -fsanitize=fuzzer-no-link)
                else()
                    set(sanitizer_test_flag -fsanitize=${sanitizer})
                endif()

                set(sanitizer_variable HAS_SANITIZER_${sanitizer})
                string(MAKE_C_IDENTIFIER ${sanitizer_variable} sanitizer_variable)

                # Need to set this here so that the flag is passed to the linker
                set(CMAKE_REQUIRED_FLAGS ${sanitizer_test_flag})
                check_c_compiler_flag(${sanitizer_test_flag} ${sanitizer_variable})
                if(${${sanitizer_variable}})
                    set(PRESENT_SANITIZERS "${PRESENT_SANITIZERS},${sanitizer}")
                endif()
            endforeach()

            target_compile_options(${target} PRIVATE -fno-omit-frame-pointer -fsanitize=${PRESENT_SANITIZERS})
            set_target_properties(${target} PROPERTIES LINK_FLAGS "-fno-omit-frame-pointer -fsanitize=${PRESENT_SANITIZERS}")

            string(REPLACE "," ";" PRESENT_SANITIZERS "${PRESENT_SANITIZERS}")
            set(${target}_SANITIZERS ${PRESENT_SANITIZERS} PARENT_SCOPE)
        endif()
    endif()
endfunction()
