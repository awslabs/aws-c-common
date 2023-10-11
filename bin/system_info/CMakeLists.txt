project(print-sys-info C)

list(APPEND CMAKE_MODULE_PATH "${CMAKE_INSTALL_PREFIX}/lib/cmake")

file(GLOB SI_SRC
        "*.c"
        )

set(SI_PROJECT_NAME print-sys-info)
add_executable(${SI_PROJECT_NAME} ${SI_SRC})
aws_set_common_properties(${SI_PROJECT_NAME})


target_include_directories(${SI_PROJECT_NAME} PUBLIC
        $<BUILD_INTERFACE:${CMAKE_CURRENT_SOURCE_DIR}/include>
        $<INSTALL_INTERFACE:include>)

target_link_libraries(${SI_PROJECT_NAME} PRIVATE aws-c-common)
