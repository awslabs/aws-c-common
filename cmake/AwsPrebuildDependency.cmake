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

    if (NOT AWS_PREBUILD_DEPENDENCY_NAME)
        message(FATAL_ERROR "Missing DEPENDENCY_NAME argument in prebuild_dependency function")
    endif()

    if (NOT AWS_PREBUILD_SOURCE_DIR)
        message(FATAL_ERROR "Missing SOURCE_DIR argument in prebuild_dependency function")
    endif()

    set(depBinaryDir ${CMAKE_BINARY_DIR}/deps/${AWS_PREBUILD_DEPENDENCY_NAME})
    set(depInstallDir ${depBinaryDir}/install)
    file(MAKE_DIRECTORY ${depBinaryDir})

    # Convert prefix path from list to escaped string, to be passed on command line
    string(REPLACE ";" "\\\\;" ESCAPED_PREFIX_PATH "${CMAKE_PREFIX_PATH}")
    # For execute_process to accept a dynamically constructed command, it should be passed in a list format.
    set(cmakeCommand "${CMAKE_COMMAND}")

    # Get the list of optional and platform-specific variables that may affect build process.
    set(cmakeOptionalVariables "")
    aws_get_variables_for_prebuild_dependency(cmakeOptionalVariables)
    list(APPEND cmakeCommand ${cmakeOptionalVariables})

    # The following variables should always be used.
    list(APPEND cmakeCommand ${AWS_PREBUILD_SOURCE_DIR})
    list(APPEND cmakeCommand -DCMAKE_BUILD_TYPE=${CMAKE_BUILD_TYPE})
    list(APPEND cmakeCommand -DCMAKE_PREFIX_PATH=${ESCAPED_PREFIX_PATH})
    list(APPEND cmakeCommand -DCMAKE_INSTALL_PREFIX=${depInstallDir})
    list(APPEND cmakeCommand -DCMAKE_INSTALL_RPATH=${CMAKE_INSTALL_RPATH})
    list(APPEND cmakeCommand -DBUILD_SHARED_LIBS=${BUILD_SHARED_LIBS})
    # In case a custom generator was provided via -G option. If we don't propagate it, the default value might
    # conflict with other cmake options (e.g. CMAKE_MAKE_PROGRAM) or no make program could be found at all.
    if (CMAKE_GENERATOR)
        list(APPEND cmakeCommand -G${CMAKE_GENERATOR})
    endif()

    # Append provided arguments to CMake command.
    if (AWS_PREBUILD_CMAKE_ARGUMENTS)
        list(APPEND cmakeCommand ${AWS_PREBUILD_CMAKE_ARGUMENTS})
    endif()

    message(STATUS "cmake command for dependency ${AWS_PREBUILD_DEPENDENCY_NAME}: ${cmakeCommand}")
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
    if (CMAKE_CROSSCOMPILING)
        list(INSERT CMAKE_FIND_ROOT_PATH 0 ${depInstallDir})
        set(CMAKE_FIND_ROOT_PATH ${CMAKE_FIND_ROOT_PATH} PARENT_SCOPE)
    endif()

    set(${AWS_PREBUILD_DEPENDENCY_NAME}_PREBUILT TRUE CACHE INTERNAL "Indicate that dependency is built and can be used")

    # Generates installation rules for the dependency project.
    # On installing targets, CMake will just copy this prebuilt version to a designated installation directory.
    install(
        DIRECTORY ${depInstallDir}/
        DESTINATION ${CMAKE_INSTALL_PREFIX}
    )
endfunction()

# Get list of optional variables that may affect build process.
function(aws_get_variables_for_prebuild_dependency AWS_CMAKE_PREBUILD_ARGS)
    set(variables "")
    set(variablesToIgnore CMAKE_INSTALL_PREFIX)

    # The CMake variables below were chosen for Unix-like platforms. If you want to use the prebuild logic on other
    # platforms, the chances are you have to handle additional variables (like CMAKE_OSX_SYSROOT).
    if (NOT UNIX OR APPLE)
        message(FATAL_ERROR "aws_get_variables_for_prebuild_dependency is called for unsupported platform")
    endif()

    get_cmake_property(vars CACHE_VARIABLES)
    foreach(var ${vars})
        message("= Checking ${var}")
        if (var MATCHES "^(CMAKE_)?ANDROID_"
                OR var STREQUAL "CMAKE_TOOLCHAIN_FILE"
                # CMAKE_CROSSCOMPILING will be set to true by CMake if the CMAKE_SYSTEM_NAME variable has been set
                # manually. By checking CMAKE_CROSSCOMPILING, we handle a possible case when CMAKE_SYSTEM_NAME was set
                # automatically to the host system.
                # CMAKE_SYSTEM_VERSION is coupled with CMAKE_SYSTEM_NAME, so apply the same logic to it.
                OR (var STREQUAL "CMAKE_SYSTEM_NAME" AND CMAKE_CROSSCOMPILING)
                OR (var STREQUAL "CMAKE_SYSTEM_VERSION" AND CMAKE_CROSSCOMPILING)
                OR var STREQUAL "CMAKE_C_COMPILER"
                OR var STREQUAL "CMAKE_CXX_COMPILER"
                OR var STREQUAL "CMAKE_C_FLAGS"
                OR var STREQUAL "CMAKE_MAKE_PROGRAM"
                OR var STREQUAL "CMAKE_RUNTIME_OUTPUT_DIRECTORY"
                OR var STREQUAL "CMAKE_LIBRARY_OUTPUT_DIRECTORY")
            set(escaped_var ${${var}})
            # To store a list within another list, it needs to be escaped first.
            string(REPLACE ";" "\\\\;" escapedVar "${${var}}")
            list(APPEND variables "-D${var}=${escapedVar}")
        endif()
    endforeach()
    set(${AWS_CMAKE_PREBUILD_ARGS} ${variables} PARENT_SCOPE)
endfunction()
