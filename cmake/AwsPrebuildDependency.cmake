# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0.

# Build given dependency project during CMake configuration step and install it into CMAKE_BINARY_DIR.
# Arguments:
#  DEPENDENCY_NAME Project name that should be built and installed.
#  SOURCE_DIR Path to the project.
#  CMAKE_ARGUMENTS Additional arguments that will be passed to cmake command.
#
# Set ${DEPENDENCY_NAME}_PREBUILT variable on success.
function(aws_prebuild_dependency)
    set(oneValueArgs DEPENDENCY_NAME SOURCE_DIR)
    set(multiValueArgs CMAKE_ARGUMENTS)
    cmake_parse_arguments(AWS_PREBUILD "" "${oneValueArgs}" "${multiValueArgs}" ${ARGN})

    if(NOT AWS_PREBUILD_DEPENDENCY_NAME)
        message(FATAL_ERROR "Missing DEPENDENCY_NAME argument in prebuild_dependency function")
    endif()

    if(NOT AWS_PREBUILD_SOURCE_DIR)
        message(FATAL_ERROR "Missing SOURCE_DIR argument in prebuild_dependency function")
    endif()

    set(depBinaryDir ${CMAKE_BINARY_DIR}/deps/${AWS_PREBUILD_DEPENDENCY_NAME})
    set(depInstallDir ${depBinaryDir}/install)
    file(MAKE_DIRECTORY ${depBinaryDir})

    # Convert prefix path from list to escaped string, to be passed on command line
    string(REPLACE ";" "\\\\;" ESCAPED_PREFIX_PATH "${CMAKE_PREFIX_PATH}")
    # For execute_process to accept a dynamically constructed command, it should be passed in a list format.
    set(cmakeCommand "${CMAKE_COMMAND}")
    list(APPEND cmakeCommand ${AWS_PREBUILD_SOURCE_DIR})
    list(APPEND cmakeCommand -DCMAKE_BUILD_TYPE=${CMAKE_BUILD_TYPE})
    list(APPEND cmakeCommand -DCMAKE_PREFIX_PATH=${ESCAPED_PREFIX_PATH})
    list(APPEND cmakeCommand -DCMAKE_INSTALL_PREFIX=${depInstallDir})
    list(APPEND cmakeCommand -DCMAKE_INSTALL_RPATH=${CMAKE_INSTALL_RPATH})
    list(APPEND cmakeCommand -DBUILD_SHARED_LIBS=${BUILD_SHARED_LIBS})

    # Append provided arguments to CMake command.
    if(AWS_PREBUILD_CMAKE_ARGUMENTS)
        list(APPEND cmakeCommand ${AWS_PREBUILD_CMAKE_ARGUMENTS})
    endif()

    # Configure dependency project.
    execute_process(
        COMMAND ${cmakeCommand}
        WORKING_DIRECTORY ${depBinaryDir}
        RESULT_VARIABLE result
    )

    if (NOT ${result} EQUAL 0)
        message(FATAL_ERROR "Configuration failed for dependency project ${AWS_PREBUILD_DEPENDENCY_NAME}")
    endif()

    # Build and install dependency project into depInstallDir directory.
    execute_process(
        COMMAND ${CMAKE_COMMAND} --build . --target install
        WORKING_DIRECTORY ${depBinaryDir}
        RESULT_VARIABLE result
    )
    if (NOT ${result} EQUAL 0)
        message(FATAL_ERROR "Build failed for dependency project ${AWS_PREBUILD_DEPENDENCY_NAME}")
    endif()

    # Make the installation visible for others.
    list(INSERT CMAKE_PREFIX_PATH 0 ${depInstallDir}/)
    set(CMAKE_PREFIX_PATH ${CMAKE_PREFIX_PATH} PARENT_SCOPE)

    set(${AWS_PREBUILD_DEPENDENCY_NAME}_PREBUILT TRUE CACHE INTERNAL "Indicate that dependency is built and can be used")

    # Generates installation rules for the dependency project.
    # On installing targets, CMake will just copy this prebuilt version to a designated installation directory.
    install(
        DIRECTORY ${depInstallDir}/
        DESTINATION ${CMAKE_INSTALL_PREFIX}
    )
endfunction()

# Get list of variables provided via command line arguments (i.e. passed as -DVARIABLE=VALUE). This function iterates
# over all variables and determines if they're provided via command line or not by checking their help strings. CMake
# sets help strings for variables provided via command line to the "No help, variable specified on the command line."
# phrase since at least v3.0.
# Via https://cmake.org/pipermail/cmake/2018-January/067002.html
#
# NOTE The project() call resets help strings for some variables (e.g. CMAKE_INSTALL_PREFIX).
#
# Populate AWS_CMAKE_CMD_ARGS with command line variables and their values.
function(aws_get_cmd_arguments_for_prebuild_dependency)
    if (AWS_CMAKE_CMD_ARGS)
        message(DEBUG "AWS_CMAKE_CMD_ARGS variable is already set, resetting it")
        set(AWS_CMAKE_CMD_ARGS "")
    endif()

    set(variables_to_ignore CMAKE_INSTALL_PREFIX)

    # project() call hides these vars.
    set(variables_to_always_collect CMAKE_TOOLCHAIN_FILE)

    get_cmake_property(vars CACHE_VARIABLES)
    foreach(var ${vars})
        get_property(currentHelpString CACHE "${var}" PROPERTY HELPSTRING)
        message(WARNING "=== aws_get_cmd_arguments_for_prebuild_dependency: processing ${var}: ${currentHelpString}")
        if ("${currentHelpString}" MATCHES "No help, variable specified on the command line."
                OR "${var}" IN_LIST variables_to_always_collect)
            if("${var}" IN_LIST variables_to_ignore)
                # TODO Remove.
                message(WARNING "Ignoring ${var}")
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
