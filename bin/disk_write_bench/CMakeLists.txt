project(disk-write-bench C)

file(GLOB DWB_SRC
        "*.c"
        )

set(DWB_PROJECT_NAME disk-write-bench)
add_executable(${DWB_PROJECT_NAME} ${DWB_SRC})
aws_set_common_properties(${DWB_PROJECT_NAME})

# fallocate(2) and O_DIRECT are Linux-specific and need _GNU_SOURCE on glibc.
target_compile_definitions(${DWB_PROJECT_NAME} PRIVATE _GNU_SOURCE)

target_link_libraries(${DWB_PROJECT_NAME} PRIVATE aws-c-common)
