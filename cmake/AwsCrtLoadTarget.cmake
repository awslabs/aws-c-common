# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0.

function(aws_load_target_default package_name)
    # try to load the lib follow BUILD_SHARED_LIBS. Fall back if not exist.
    if (BUILD_SHARED_LIBS)
        if (EXISTS "${CMAKE_CURRENT_LIST_DIR}/shared")
            include(${CMAKE_CURRENT_LIST_DIR}/shared/${package_name}-targets.cmake)
        else()
            include(${CMAKE_CURRENT_LIST_DIR}/static/${package_name}-targets.cmake)
        endif()
    else()
        if (EXISTS "${CMAKE_CURRENT_LIST_DIR}/static")
            include(${CMAKE_CURRENT_LIST_DIR}/static/${package_name}-targets.cmake)
        else()
            include(${CMAKE_CURRENT_LIST_DIR}/shared/${package_name}-targets.cmake)
        endif()
    endif()
endfunction()
