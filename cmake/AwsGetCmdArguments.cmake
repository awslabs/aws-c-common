# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0.

# Get list of variables provided via command line arguments (i.e. -DVARIABLE=VALUE). This function iterates over all
# variables and determines if they're provided via command line or not by checking their help strings. CMake sets help
# strings for variables provided via command line to the "No help, variable specified on the command line." phrase since
# at least v3.0.
# Via https://cmake.org/pipermail/cmake/2018-January/067002.html
#
# MUST be done before call to 'project'. The reason is that project() resets help strings for some variables
# (e.g. CMAKE_INSTALL_PREFIX).
# 
# Populate AWS_CMAKE_CMD_ARGS with command line variables and their values.
function(aws_get_cmd_arguments)
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
            set(escaped_var ${${var}})
            # To store a list within another list, it needs to be escaped first.
            string(REPLACE ";" "\\\\;" escaped_var "${${var}}")
            list(APPEND AWS_CMAKE_CMD_ARGS "-D${var}=${escaped_var}")
        endif()
    endforeach()
    # Store cmd variables in the cache.
    set(AWS_CMAKE_CMD_ARGS ${AWS_CMAKE_CMD_ARGS} CACHE STRING "Command line variables" FORCE)
endfunction()
