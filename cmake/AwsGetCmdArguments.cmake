# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0.

# Get list of variables provided via command line arguments (i.e. -DVARIABLE=VALUE). This function iterates over all
# variables and determines if they're provided via command line or not by checking their help strings. CMake sets help
# strings for variables provided via command line to the "No help, variable specified on the command line." phrase since
# at least v3.0.
# Via https://cmake.org/pipermail/cmake/2018-January/067002.html
# Arguments:
#  VARS_TO_IGNORE Variables that should be ignored even if they were provided via command line. Multiple variables can
#                 be specified separated by space.
#
# MUST be done before call to 'project'. The reason is that project() resets help strings for some variables
# (e.g. CMAKE_INSTALL_PREFIX).
# 
# Populate AWS_CMAKE_CMD_ARGS with command line variables and their values.
function(aws_get_cmd_arguments)
    set(multiValueArgs VARS_TO_IGNORE)
    cmake_parse_arguments(AWS_GET_CMD_ARGS "" "" "${multiValueArgs}" ${ARGN})

    if (AWS_GET_CMD_ARGS_VARS_TO_IGNORE)
        message(STATUS "Ignored vars: ${AWS_GET_CMD_ARGS_VARS_TO_IGNORE}")
    endif()

    if (PROJECT_NAME)
        message(WARNING "aws_get_cmd_arguments is called after project(), some variables may be missed")
    endif()

    if (AWS_CMAKE_CMD_ARGS)
        message(STATUS "AWS_CMAKE_CMD_ARGS variable is already set, resetting it")
        set(AWS_CMAKE_CMD_ARGS "")
    endif()

    get_cmake_property(vars CACHE_VARIABLES)
    foreach(var ${vars})
        get_property(currentHelpString CACHE "${var}" PROPERTY HELPSTRING)
        if ("${currentHelpString}" MATCHES "No help, variable specified on the command line.")
            if("${var}" IN_LIST AWS_GET_CMD_ARGS_VARS_TO_IGNORE)
                continue()
            endif()
            set(escaped_var ${${var}})
            # To store a list within another list, it needs to be escaped first.
            string(REPLACE ";" "\\\\;" escaped_var "${${var}}")
            list(APPEND AWS_CMAKE_CMD_ARGS "-D${var}=${escaped_var}")
        endif()
    endforeach()
    # Store cmd variables in the cache.
    set(AWS_CMAKE_CMD_ARGS ${AWS_CMAKE_CMD_ARGS} CACHE STRING "Command line variables" FORCE)
endfunction()
