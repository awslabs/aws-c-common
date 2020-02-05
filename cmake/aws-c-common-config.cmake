@PACKAGE_INIT@

list(APPEND CMAKE_MODULE_PATH "@PACKAGE_AWS_MODULE_INSTALL_DIR@")

set(THREADS_PREFER_PTHREAD_FLAG ON)

if(WIN32 OR UNIX OR APPLE)
    find_package(Threads REQUIRED)
endif()

if (BUILD_SHARED_LIBS)
    include(${CMAKE_CURRENT_LIST_DIR}/shared/@PROJECT_NAME@-targets.cmake)
else()
    include(${CMAKE_CURRENT_LIST_DIR}/static/@PROJECT_NAME@-targets.cmake)
endif()

