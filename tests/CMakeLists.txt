enable_testing()

file(GLOB TEST_SRC "*.c")
file(GLOB TEST_HDRS "*.h")
file(GLOB TESTS ${TEST_HDRS} ${TEST_SRC})

set(TEST_BINARY_NAME ${CMAKE_PROJECT_NAME}-tests)

add_executable(${TEST_BINARY_NAME} ${TESTS})
target_link_libraries(${TEST_BINARY_NAME} ${CMAKE_PROJECT_NAME})
set_target_properties(${TEST_BINARY_NAME} PROPERTIES LINKER_LANGUAGE C C_STANDARD 99)

target_include_directories(${TEST_BINARY_NAME} PRIVATE ${CMAKE_CURRENT_LIST_DIR})

add_test(raise_errors_test ${TEST_BINARY_NAME} raise_errors_test)
add_test(reset_errors_test ${TEST_BINARY_NAME} reset_errors_test)
add_test(error_callback_test ${TEST_BINARY_NAME} error_callback_test)
add_test(unknown_error_code_in_slot_test ${TEST_BINARY_NAME} unknown_error_code_in_slot_test)
add_test(unknown_error_code_no_slot_test ${TEST_BINARY_NAME} unknown_error_code_no_slot_test)
add_test(unknown_error_code_range_too_large_test ${TEST_BINARY_NAME} unknown_error_code_range_too_large_test)
add_test(thread_creation_join_test ${TEST_BINARY_NAME} thread_creation_join_test)
add_test(thread_creation_detach_test ${TEST_BINARY_NAME} thread_creation_detach_test)
add_test(mutex_aquire_release_test ${TEST_BINARY_NAME} mutex_aquire_release_test)
add_test(mutex_is_actually_mutex_test ${TEST_BINARY_NAME} mutex_is_actually_mutex_test)
add_test(high_res_clock_increments_test ${TEST_BINARY_NAME} high_res_clock_increments_test)
add_test(sys_clock_increments_test ${TEST_BINARY_NAME} sys_clock_increments_test)
add_test(error_code_cross_thread_test, ${TEST_BINARY_NAME} error_code_cross_thread_test)
