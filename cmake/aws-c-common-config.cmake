# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0.

include(AwsCrtLoadTarget)

set(THREADS_PREFER_PTHREAD_FLAG ON)

if(WIN32 OR UNIX OR APPLE)
    find_package(Threads REQUIRED)
endif()

aws_load_target_default(@PROJECT_NAME@)
