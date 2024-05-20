/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */
#include <aws/common/uri.h>
#include <aws/testing/aws_test_harness.h>

static int s_test_uri_full_parse(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;
    const char *str_uri = "https://some_user:some_password@www.test.com:8443/path/to/"
                          "resource?test1=value1&test%20space=value%20space&test2=value2&test2=value3";

    struct aws_byte_cursor uri_csr = aws_byte_cursor_from_c_str(str_uri);
    struct aws_uri uri;
    ASSERT_SUCCESS(aws_uri_init_parse(&uri, allocator, &uri_csr));

    struct aws_byte_cursor expected_scheme = aws_byte_cursor_from_c_str("https");
    ASSERT_BIN_ARRAYS_EQUALS(expected_scheme.ptr, expected_scheme.len, uri.scheme.ptr, uri.scheme.len);

    struct aws_byte_cursor expected_authority = aws_byte_cursor_from_c_str("some_user:some_password@www.test.com:8443");
    ASSERT_BIN_ARRAYS_EQUALS(expected_authority.ptr, expected_authority.len, uri.authority.ptr, uri.authority.len);

    struct aws_byte_cursor expected_userinfo = aws_byte_cursor_from_c_str("some_user:some_password");
    ASSERT_BIN_ARRAYS_EQUALS(expected_userinfo.ptr, expected_userinfo.len, uri.userinfo.ptr, uri.userinfo.len);

    struct aws_byte_cursor expected_user = aws_byte_cursor_from_c_str("some_user");
    ASSERT_BIN_ARRAYS_EQUALS(expected_user.ptr, expected_user.len, uri.user.ptr, uri.user.len);

    struct aws_byte_cursor expected_password = aws_byte_cursor_from_c_str("some_password");
    ASSERT_BIN_ARRAYS_EQUALS(expected_password.ptr, expected_password.len, uri.password.ptr, uri.password.len);

    struct aws_byte_cursor expected_host = aws_byte_cursor_from_c_str("www.test.com");
    ASSERT_BIN_ARRAYS_EQUALS(expected_host.ptr, expected_host.len, uri.host_name.ptr, uri.host_name.len);

    ASSERT_UINT_EQUALS(8443, uri.port);

    struct aws_byte_cursor expected_path = aws_byte_cursor_from_c_str("/path/to/resource");
    ASSERT_BIN_ARRAYS_EQUALS(expected_path.ptr, expected_path.len, uri.path.ptr, uri.path.len);

    struct aws_byte_cursor expected_query_str =
        aws_byte_cursor_from_c_str("test1=value1&test%20space=value%20space&test2=value2&test2=value3");
    ASSERT_BIN_ARRAYS_EQUALS(
        expected_query_str.ptr, expected_query_str.len, uri.query_string.ptr, uri.query_string.len);

    struct aws_byte_cursor expected_request_uri = aws_byte_cursor_from_c_str(
        "/path/to/resource?test1=value1&test%20space=value%20space&test2=value2&test2=value3");
    ASSERT_BIN_ARRAYS_EQUALS(
        expected_request_uri.ptr, expected_request_uri.len, uri.path_and_query.ptr, uri.path_and_query.len);

    aws_uri_clean_up(&uri);
    return AWS_OP_SUCCESS;
}

AWS_TEST_CASE(uri_full_parse, s_test_uri_full_parse);

static int s_test_uri_no_scheme_parse(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;
    const char *str_uri =
        "www.test.com:8443/path/to/resource?test1=value1&test%20space=value%20space&test2=value2&test2=value3";

    struct aws_byte_cursor uri_csr = aws_byte_cursor_from_c_str(str_uri);
    struct aws_uri uri;
    ASSERT_SUCCESS(aws_uri_init_parse(&uri, allocator, &uri_csr));

    ASSERT_UINT_EQUALS(0U, uri.scheme.len);

    struct aws_byte_cursor expected_authority = aws_byte_cursor_from_c_str("www.test.com:8443");
    ASSERT_BIN_ARRAYS_EQUALS(expected_authority.ptr, expected_authority.len, uri.authority.ptr, uri.authority.len);

    struct aws_byte_cursor expected_host = aws_byte_cursor_from_c_str("www.test.com");
    ASSERT_BIN_ARRAYS_EQUALS(expected_host.ptr, expected_host.len, uri.host_name.ptr, uri.host_name.len);

    ASSERT_UINT_EQUALS(8443, uri.port);

    struct aws_byte_cursor expected_path = aws_byte_cursor_from_c_str("/path/to/resource");
    ASSERT_BIN_ARRAYS_EQUALS(expected_path.ptr, expected_path.len, uri.path.ptr, uri.path.len);

    struct aws_byte_cursor expected_query_str =
        aws_byte_cursor_from_c_str("test1=value1&test%20space=value%20space&test2=value2&test2=value3");
    ASSERT_BIN_ARRAYS_EQUALS(
        expected_query_str.ptr, expected_query_str.len, uri.query_string.ptr, uri.query_string.len);

    struct aws_byte_cursor expected_request_uri = aws_byte_cursor_from_c_str(
        "/path/to/resource?test1=value1&test%20space=value%20space&test2=value2&test2=value3");
    ASSERT_BIN_ARRAYS_EQUALS(
        expected_request_uri.ptr, expected_request_uri.len, uri.path_and_query.ptr, uri.path_and_query.len);

    aws_uri_clean_up(&uri);
    return AWS_OP_SUCCESS;
}

AWS_TEST_CASE(uri_no_scheme_parse, s_test_uri_no_scheme_parse);

static int s_test_uri_no_port_parse(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;
    const char *str_uri =
        "https://www.test.com/path/to/resource?test1=value1&test%20space=value%20space&test2=value2&test2=value3";

    struct aws_byte_cursor uri_csr = aws_byte_cursor_from_c_str(str_uri);
    struct aws_uri uri;
    ASSERT_SUCCESS(aws_uri_init_parse(&uri, allocator, &uri_csr));

    struct aws_byte_cursor expected_scheme = aws_byte_cursor_from_c_str("https");
    ASSERT_BIN_ARRAYS_EQUALS(expected_scheme.ptr, expected_scheme.len, uri.scheme.ptr, uri.scheme.len);

    struct aws_byte_cursor expected_authority = aws_byte_cursor_from_c_str("www.test.com");
    ASSERT_BIN_ARRAYS_EQUALS(expected_authority.ptr, expected_authority.len, uri.authority.ptr, uri.authority.len);

    struct aws_byte_cursor expected_host = aws_byte_cursor_from_c_str("www.test.com");
    ASSERT_BIN_ARRAYS_EQUALS(expected_host.ptr, expected_host.len, uri.host_name.ptr, uri.host_name.len);

    ASSERT_UINT_EQUALS(0, uri.port);

    struct aws_byte_cursor expected_path = aws_byte_cursor_from_c_str("/path/to/resource");
    ASSERT_BIN_ARRAYS_EQUALS(expected_path.ptr, expected_path.len, uri.path.ptr, uri.path.len);

    struct aws_byte_cursor expected_query_str =
        aws_byte_cursor_from_c_str("test1=value1&test%20space=value%20space&test2=value2&test2=value3");
    ASSERT_BIN_ARRAYS_EQUALS(
        expected_query_str.ptr, expected_query_str.len, uri.query_string.ptr, uri.query_string.len);

    struct aws_byte_cursor expected_request_uri = aws_byte_cursor_from_c_str(
        "/path/to/resource?test1=value1&test%20space=value%20space&test2=value2&test2=value3");
    ASSERT_BIN_ARRAYS_EQUALS(
        expected_request_uri.ptr, expected_request_uri.len, uri.path_and_query.ptr, uri.path_and_query.len);

    aws_uri_clean_up(&uri);
    return AWS_OP_SUCCESS;
}

AWS_TEST_CASE(uri_no_port_parse, s_test_uri_no_port_parse);

static int s_test_uri_no_path_parse(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;
    const char *str_uri =
        "https://www.test.com:8443/?test1=value1&test%20space=value%20space&test2=value2&test2=value3";

    struct aws_byte_cursor uri_csr = aws_byte_cursor_from_c_str(str_uri);
    struct aws_uri uri;
    ASSERT_SUCCESS(aws_uri_init_parse(&uri, allocator, &uri_csr));

    struct aws_byte_cursor expected_scheme = aws_byte_cursor_from_c_str("https");
    ASSERT_BIN_ARRAYS_EQUALS(expected_scheme.ptr, expected_scheme.len, uri.scheme.ptr, uri.scheme.len);

    struct aws_byte_cursor expected_authority = aws_byte_cursor_from_c_str("www.test.com:8443");
    ASSERT_BIN_ARRAYS_EQUALS(expected_authority.ptr, expected_authority.len, uri.authority.ptr, uri.authority.len);

    struct aws_byte_cursor expected_host = aws_byte_cursor_from_c_str("www.test.com");
    ASSERT_BIN_ARRAYS_EQUALS(expected_host.ptr, expected_host.len, uri.host_name.ptr, uri.host_name.len);

    ASSERT_UINT_EQUALS(8443, uri.port);

    struct aws_byte_cursor expected_path = aws_byte_cursor_from_c_str("/");
    ASSERT_BIN_ARRAYS_EQUALS(expected_path.ptr, expected_path.len, uri.path.ptr, uri.path.len);

    struct aws_byte_cursor expected_query_str =
        aws_byte_cursor_from_c_str("test1=value1&test%20space=value%20space&test2=value2&test2=value3");
    ASSERT_BIN_ARRAYS_EQUALS(
        expected_query_str.ptr, expected_query_str.len, uri.query_string.ptr, uri.query_string.len);

    struct aws_byte_cursor expected_request_uri =
        aws_byte_cursor_from_c_str("/?test1=value1&test%20space=value%20space&test2=value2&test2=value3");
    ASSERT_BIN_ARRAYS_EQUALS(
        expected_request_uri.ptr, expected_request_uri.len, uri.path_and_query.ptr, uri.path_and_query.len);
    aws_uri_clean_up(&uri);
    return AWS_OP_SUCCESS;
}

AWS_TEST_CASE(uri_no_path_parse, s_test_uri_no_path_parse);

static int s_test_uri_no_query_parse(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;
    const char *str_uri = "https://www.test.com:8443/path/to/resource";

    struct aws_byte_cursor uri_csr = aws_byte_cursor_from_c_str(str_uri);
    struct aws_uri uri;
    ASSERT_SUCCESS(aws_uri_init_parse(&uri, allocator, &uri_csr));

    struct aws_byte_cursor expected_scheme = aws_byte_cursor_from_c_str("https");
    ASSERT_BIN_ARRAYS_EQUALS(expected_scheme.ptr, expected_scheme.len, uri.scheme.ptr, uri.scheme.len);

    struct aws_byte_cursor expected_authority = aws_byte_cursor_from_c_str("www.test.com:8443");
    ASSERT_BIN_ARRAYS_EQUALS(expected_authority.ptr, expected_authority.len, uri.authority.ptr, uri.authority.len);

    struct aws_byte_cursor expected_host = aws_byte_cursor_from_c_str("www.test.com");
    ASSERT_BIN_ARRAYS_EQUALS(expected_host.ptr, expected_host.len, uri.host_name.ptr, uri.host_name.len);

    ASSERT_UINT_EQUALS(8443, uri.port);

    struct aws_byte_cursor expected_path = aws_byte_cursor_from_c_str("/path/to/resource");
    ASSERT_BIN_ARRAYS_EQUALS(expected_path.ptr, expected_path.len, uri.path.ptr, uri.path.len);

    struct aws_byte_cursor expected_request_uri = aws_byte_cursor_from_c_str("/path/to/resource");
    ASSERT_BIN_ARRAYS_EQUALS(
        expected_request_uri.ptr, expected_request_uri.len, uri.path_and_query.ptr, uri.path_and_query.len);

    ASSERT_UINT_EQUALS(0U, uri.query_string.len);

    aws_uri_clean_up(&uri);
    return AWS_OP_SUCCESS;
}

AWS_TEST_CASE(uri_no_query_parse, s_test_uri_no_query_parse);

static int s_test_uri_minimal_parse(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;
    const char *str_uri = "www.test.com/path/to/resource";

    struct aws_byte_cursor uri_csr = aws_byte_cursor_from_c_str(str_uri);
    struct aws_uri uri;
    ASSERT_SUCCESS(aws_uri_init_parse(&uri, allocator, &uri_csr));

    ASSERT_UINT_EQUALS(0U, uri.scheme.len);

    struct aws_byte_cursor expected_authority = aws_byte_cursor_from_c_str("www.test.com");
    ASSERT_BIN_ARRAYS_EQUALS(expected_authority.ptr, expected_authority.len, uri.authority.ptr, uri.authority.len);

    struct aws_byte_cursor expected_host = aws_byte_cursor_from_c_str("www.test.com");
    ASSERT_BIN_ARRAYS_EQUALS(expected_host.ptr, expected_host.len, uri.host_name.ptr, uri.host_name.len);

    ASSERT_UINT_EQUALS(0, uri.port);

    struct aws_byte_cursor expected_path = aws_byte_cursor_from_c_str("/path/to/resource");
    ASSERT_BIN_ARRAYS_EQUALS(expected_path.ptr, expected_path.len, uri.path.ptr, uri.path.len);

    struct aws_byte_cursor expected_request_uri = aws_byte_cursor_from_c_str("/path/to/resource");
    ASSERT_BIN_ARRAYS_EQUALS(
        expected_request_uri.ptr, expected_request_uri.len, uri.path_and_query.ptr, uri.path_and_query.len);

    ASSERT_UINT_EQUALS(0U, uri.query_string.len);

    aws_uri_clean_up(&uri);
    return AWS_OP_SUCCESS;
}

AWS_TEST_CASE(uri_minimal_parse, s_test_uri_minimal_parse);

static int s_test_uri_path_and_query_only_parse(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;
    const char *str_uri = "/path/to/resource?test1=value1&test%20space=value%20space&test2=value2&test2=value3";

    struct aws_byte_cursor uri_csr = aws_byte_cursor_from_c_str(str_uri);
    struct aws_uri uri;
    ASSERT_SUCCESS(aws_uri_init_parse(&uri, allocator, &uri_csr));

    ASSERT_UINT_EQUALS(0U, uri.scheme.len);
    ASSERT_UINT_EQUALS(0U, uri.authority.len);

    struct aws_byte_cursor expected_path = aws_byte_cursor_from_c_str("/path/to/resource");
    ASSERT_BIN_ARRAYS_EQUALS(expected_path.ptr, expected_path.len, uri.path.ptr, uri.path.len);

    struct aws_byte_cursor expected_query_str =
        aws_byte_cursor_from_c_str("test1=value1&test%20space=value%20space&test2=value2&test2=value3");
    ASSERT_BIN_ARRAYS_EQUALS(
        expected_query_str.ptr, expected_query_str.len, uri.query_string.ptr, uri.query_string.len);

    struct aws_byte_cursor expected_path_and_query = aws_byte_cursor_from_c_str(
        "/path/to/resource?test1=value1&test%20space=value%20space&test2=value2&test2=value3");
    ASSERT_BIN_ARRAYS_EQUALS(
        expected_path_and_query.ptr, expected_path_and_query.len, uri.path_and_query.ptr, uri.path_and_query.len);

    aws_uri_clean_up(&uri);
    return AWS_OP_SUCCESS;
}

AWS_TEST_CASE(uri_path_and_query_only_parse, s_test_uri_path_and_query_only_parse);

static int s_test_uri_root_only_parse(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;
    const char *str_uri = "https://www.test.com";

    struct aws_byte_cursor uri_csr = aws_byte_cursor_from_c_str(str_uri);
    struct aws_uri uri;
    ASSERT_SUCCESS(aws_uri_init_parse(&uri, allocator, &uri_csr));

    struct aws_byte_cursor expected_scheme = aws_byte_cursor_from_c_str("https");
    ASSERT_BIN_ARRAYS_EQUALS(expected_scheme.ptr, expected_scheme.len, uri.scheme.ptr, uri.scheme.len);

    struct aws_byte_cursor expected_authority = aws_byte_cursor_from_c_str("www.test.com");
    ASSERT_BIN_ARRAYS_EQUALS(expected_authority.ptr, expected_authority.len, uri.authority.ptr, uri.authority.len);

    struct aws_byte_cursor expected_host = aws_byte_cursor_from_c_str("www.test.com");
    ASSERT_BIN_ARRAYS_EQUALS(expected_host.ptr, expected_host.len, uri.host_name.ptr, uri.host_name.len);

    ASSERT_UINT_EQUALS(0, uri.port);

    struct aws_byte_cursor expected_path = aws_byte_cursor_from_c_str("");
    ASSERT_BIN_ARRAYS_EQUALS(expected_path.ptr, expected_path.len, uri.path.ptr, uri.path.len);

    ASSERT_UINT_EQUALS(0U, uri.query_string.len);

    aws_uri_clean_up(&uri);
    return AWS_OP_SUCCESS;
}

AWS_TEST_CASE(uri_root_only_parse, s_test_uri_root_only_parse);

static int s_test_uri_root_slash_only_path_parse(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;
    const char *str_uri = "https://www.test.com/";

    struct aws_byte_cursor uri_csr = aws_byte_cursor_from_c_str(str_uri);
    struct aws_uri uri;
    ASSERT_SUCCESS(aws_uri_init_parse(&uri, allocator, &uri_csr));

    struct aws_byte_cursor expected_scheme = aws_byte_cursor_from_c_str("https");
    ASSERT_BIN_ARRAYS_EQUALS(expected_scheme.ptr, expected_scheme.len, uri.scheme.ptr, uri.scheme.len);

    struct aws_byte_cursor expected_authority = aws_byte_cursor_from_c_str("www.test.com");
    ASSERT_BIN_ARRAYS_EQUALS(expected_authority.ptr, expected_authority.len, uri.authority.ptr, uri.authority.len);

    struct aws_byte_cursor expected_host = aws_byte_cursor_from_c_str("www.test.com");
    ASSERT_BIN_ARRAYS_EQUALS(expected_host.ptr, expected_host.len, uri.host_name.ptr, uri.host_name.len);

    ASSERT_UINT_EQUALS(0, uri.port);

    struct aws_byte_cursor expected_path = aws_byte_cursor_from_c_str("/");
    ASSERT_BIN_ARRAYS_EQUALS(expected_path.ptr, expected_path.len, uri.path.ptr, uri.path.len);

    ASSERT_UINT_EQUALS(0U, uri.query_string.len);

    aws_uri_clean_up(&uri);
    return AWS_OP_SUCCESS;
}

AWS_TEST_CASE(uri_root_slash_only_path_parse, s_test_uri_root_slash_only_path_parse);

static int s_test_uri_userinfo_no_password_parse(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;
    /* RFC-3986 section 3.2.1: Use of the format "user:password" in the userinfo field is deprecated.
     * We will try to parse the userinfo with the format still, but if not happening, it will not be treated as an
     * error. The whole userinfo will still be available to access */
    const char *str_uri = "https://some_name@www.test.com";

    struct aws_byte_cursor uri_csr = aws_byte_cursor_from_c_str(str_uri);
    struct aws_uri uri;
    ASSERT_SUCCESS(aws_uri_init_parse(&uri, allocator, &uri_csr));

    struct aws_byte_cursor expected_scheme = aws_byte_cursor_from_c_str("https");
    ASSERT_BIN_ARRAYS_EQUALS(expected_scheme.ptr, expected_scheme.len, uri.scheme.ptr, uri.scheme.len);

    struct aws_byte_cursor expected_authority = aws_byte_cursor_from_c_str("some_name@www.test.com");
    ASSERT_BIN_ARRAYS_EQUALS(expected_authority.ptr, expected_authority.len, uri.authority.ptr, uri.authority.len);

    struct aws_byte_cursor expected_userinfo = aws_byte_cursor_from_c_str("some_name");
    ASSERT_BIN_ARRAYS_EQUALS(expected_userinfo.ptr, expected_userinfo.len, uri.userinfo.ptr, uri.userinfo.len);

    struct aws_byte_cursor expected_user = aws_byte_cursor_from_c_str("some_name");
    ASSERT_BIN_ARRAYS_EQUALS(expected_user.ptr, expected_user.len, uri.user.ptr, uri.user.len);
    ASSERT_UINT_EQUALS(0U, uri.password.len);

    struct aws_byte_cursor expected_host = aws_byte_cursor_from_c_str("www.test.com");
    ASSERT_BIN_ARRAYS_EQUALS(expected_host.ptr, expected_host.len, uri.host_name.ptr, uri.host_name.len);

    ASSERT_UINT_EQUALS(0, uri.port);

    struct aws_byte_cursor expected_path = aws_byte_cursor_from_c_str("");
    ASSERT_BIN_ARRAYS_EQUALS(expected_path.ptr, expected_path.len, uri.path.ptr, uri.path.len);

    ASSERT_UINT_EQUALS(0U, uri.query_string.len);

    aws_uri_clean_up(&uri);
    return AWS_OP_SUCCESS;
}

AWS_TEST_CASE(uri_userinfo_no_password_parse, s_test_uri_userinfo_no_password_parse);

static int s_test_uri_empty_user_parse(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;
    /* RFC-3986 section 3.2.1: Use of the format "user:password" in the userinfo field is deprecated.
     * We will try to parse the userinfo with the format still, but if not happening, it will not be treated as an
     * error. The whole userinfo will still be available to access */
    const char *str_uri = "https://@www.test.com";

    struct aws_byte_cursor uri_csr = aws_byte_cursor_from_c_str(str_uri);
    struct aws_uri uri;
    ASSERT_SUCCESS(aws_uri_init_parse(&uri, allocator, &uri_csr));

    struct aws_byte_cursor expected_scheme = aws_byte_cursor_from_c_str("https");
    ASSERT_BIN_ARRAYS_EQUALS(expected_scheme.ptr, expected_scheme.len, uri.scheme.ptr, uri.scheme.len);

    struct aws_byte_cursor expected_authority = aws_byte_cursor_from_c_str("@www.test.com");
    ASSERT_BIN_ARRAYS_EQUALS(expected_authority.ptr, expected_authority.len, uri.authority.ptr, uri.authority.len);

    ASSERT_UINT_EQUALS(0U, uri.userinfo.len);
    ASSERT_UINT_EQUALS(0U, uri.user.len);
    ASSERT_UINT_EQUALS(0U, uri.password.len);

    struct aws_byte_cursor expected_host = aws_byte_cursor_from_c_str("www.test.com");
    ASSERT_BIN_ARRAYS_EQUALS(expected_host.ptr, expected_host.len, uri.host_name.ptr, uri.host_name.len);

    ASSERT_UINT_EQUALS(0, uri.port);

    struct aws_byte_cursor expected_path = aws_byte_cursor_from_c_str("");
    ASSERT_BIN_ARRAYS_EQUALS(expected_path.ptr, expected_path.len, uri.path.ptr, uri.path.len);

    ASSERT_UINT_EQUALS(0U, uri.query_string.len);

    aws_uri_clean_up(&uri);
    return AWS_OP_SUCCESS;
}

AWS_TEST_CASE(uri_empty_user_parse, s_test_uri_empty_user_parse);

static int s_test_uri_query_params(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;
    const char *str_uri = "https://www.test.com:8443/path/to/"
                          "resource?test1=value1&testkeyonly&&test%20space=value%20space&test2=value2&test2=value3";

    struct aws_byte_cursor uri_csr = aws_byte_cursor_from_c_str(str_uri);
    struct aws_uri uri;
    ASSERT_SUCCESS(aws_uri_init_parse(&uri, allocator, &uri_csr));

    struct aws_uri_param params[5];
    AWS_ZERO_ARRAY(params);
    struct aws_array_list params_list;
    aws_array_list_init_static(&params_list, &params, 5, sizeof(struct aws_uri_param));

    ASSERT_SUCCESS(aws_uri_query_string_params(&uri, &params_list));
    ASSERT_UINT_EQUALS(5u, aws_array_list_length(&params_list));

    struct aws_byte_cursor expected_key = aws_byte_cursor_from_c_str("test1");
    struct aws_byte_cursor expected_value = aws_byte_cursor_from_c_str("value1");

    ASSERT_BIN_ARRAYS_EQUALS(expected_key.ptr, expected_key.len, params[0].key.ptr, params[0].key.len);
    ASSERT_BIN_ARRAYS_EQUALS(expected_value.ptr, expected_value.len, params[0].value.ptr, params[0].value.len);

    expected_key = aws_byte_cursor_from_c_str("testkeyonly");

    ASSERT_BIN_ARRAYS_EQUALS(expected_key.ptr, expected_key.len, params[1].key.ptr, params[1].key.len);
    ASSERT_UINT_EQUALS(0U, params[1].value.len);

    expected_key = aws_byte_cursor_from_c_str("test%20space");
    expected_value = aws_byte_cursor_from_c_str("value%20space");

    ASSERT_BIN_ARRAYS_EQUALS(expected_key.ptr, expected_key.len, params[2].key.ptr, params[2].key.len);
    ASSERT_BIN_ARRAYS_EQUALS(expected_value.ptr, expected_value.len, params[2].value.ptr, params[2].value.len);

    expected_key = aws_byte_cursor_from_c_str("test2");
    expected_value = aws_byte_cursor_from_c_str("value2");

    ASSERT_BIN_ARRAYS_EQUALS(expected_key.ptr, expected_key.len, params[3].key.ptr, params[3].key.len);
    ASSERT_BIN_ARRAYS_EQUALS(expected_value.ptr, expected_value.len, params[3].value.ptr, params[3].value.len);

    expected_key = aws_byte_cursor_from_c_str("test2");
    expected_value = aws_byte_cursor_from_c_str("value3");

    ASSERT_BIN_ARRAYS_EQUALS(expected_key.ptr, expected_key.len, params[4].key.ptr, params[4].key.len);
    ASSERT_BIN_ARRAYS_EQUALS(expected_value.ptr, expected_value.len, params[4].value.ptr, params[4].value.len);

    aws_uri_clean_up(&uri);

    /* Test empty query string */
    str_uri = "https://www.test.com:8443/path/to/resource";
    uri_csr = aws_byte_cursor_from_c_str(str_uri);
    ASSERT_SUCCESS(aws_uri_init_parse(&uri, allocator, &uri_csr));
    aws_array_list_clear(&params_list);
    ASSERT_SUCCESS(aws_uri_query_string_params(&uri, &params_list));
    ASSERT_UINT_EQUALS(0, aws_array_list_length(&params_list));
    aws_uri_clean_up(&uri);

    return AWS_OP_SUCCESS;
}

AWS_TEST_CASE(uri_query_params, s_test_uri_query_params);

static int s_test_uri_ipv4_parse(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;
    const char *str_uri = "https://127.0.0.1:8443";

    struct aws_byte_cursor uri_csr = aws_byte_cursor_from_c_str(str_uri);
    struct aws_uri uri;
    ASSERT_SUCCESS(aws_uri_init_parse(&uri, allocator, &uri_csr));

    struct aws_byte_cursor expected_scheme = aws_byte_cursor_from_c_str("https");
    ASSERT_BIN_ARRAYS_EQUALS(expected_scheme.ptr, expected_scheme.len, uri.scheme.ptr, uri.scheme.len);

    struct aws_byte_cursor expected_authority = aws_byte_cursor_from_c_str("127.0.0.1:8443");
    ASSERT_BIN_ARRAYS_EQUALS(expected_authority.ptr, expected_authority.len, uri.authority.ptr, uri.authority.len);

    struct aws_byte_cursor expected_host = aws_byte_cursor_from_c_str("127.0.0.1");
    ASSERT_BIN_ARRAYS_EQUALS(expected_host.ptr, expected_host.len, uri.host_name.ptr, uri.host_name.len);

    ASSERT_UINT_EQUALS(8443, uri.port);

    struct aws_byte_cursor expected_path = aws_byte_cursor_from_c_str("");
    ASSERT_BIN_ARRAYS_EQUALS(expected_path.ptr, expected_path.len, uri.path.ptr, uri.path.len);

    ASSERT_UINT_EQUALS(0U, uri.query_string.len);

    aws_uri_clean_up(&uri);
    return AWS_OP_SUCCESS;
}

AWS_TEST_CASE(uri_ipv4_parse, s_test_uri_ipv4_parse);

static int s_test_uri_ipv6_parse(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;
    const char *str_uri = "https://[2001:db8:85a3:8d3:1319:8a2e:370:7348%25en0]:443";

    struct aws_byte_cursor uri_csr = aws_byte_cursor_from_c_str(str_uri);
    struct aws_uri uri;
    ASSERT_SUCCESS(aws_uri_init_parse(&uri, allocator, &uri_csr));

    struct aws_byte_cursor expected_scheme = aws_byte_cursor_from_c_str("https");
    ASSERT_BIN_ARRAYS_EQUALS(expected_scheme.ptr, expected_scheme.len, uri.scheme.ptr, uri.scheme.len);

    struct aws_byte_cursor expected_authority =
        aws_byte_cursor_from_c_str("[2001:db8:85a3:8d3:1319:8a2e:370:7348%25en0]:443");
    ASSERT_BIN_ARRAYS_EQUALS(expected_authority.ptr, expected_authority.len, uri.authority.ptr, uri.authority.len);

    struct aws_byte_cursor expected_host = aws_byte_cursor_from_c_str("2001:db8:85a3:8d3:1319:8a2e:370:7348%25en0");
    ASSERT_BIN_ARRAYS_EQUALS(expected_host.ptr, expected_host.len, uri.host_name.ptr, uri.host_name.len);

    ASSERT_UINT_EQUALS(443, uri.port);

    struct aws_byte_cursor expected_path = aws_byte_cursor_from_c_str("");
    ASSERT_BIN_ARRAYS_EQUALS(expected_path.ptr, expected_path.len, uri.path.ptr, uri.path.len);

    ASSERT_UINT_EQUALS(0U, uri.query_string.len);

    aws_uri_clean_up(&uri);
    return AWS_OP_SUCCESS;
}

AWS_TEST_CASE(uri_ipv6_parse, s_test_uri_ipv6_parse);

static int s_test_uri_ipv6_no_port_parse(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;
    const char *str_uri = "https://[2001:db8:85a3:8d3:1319:8a2e:370:7348%25en0]";

    struct aws_byte_cursor uri_csr = aws_byte_cursor_from_c_str(str_uri);
    struct aws_uri uri;
    ASSERT_SUCCESS(aws_uri_init_parse(&uri, allocator, &uri_csr));

    struct aws_byte_cursor expected_scheme = aws_byte_cursor_from_c_str("https");
    ASSERT_BIN_ARRAYS_EQUALS(expected_scheme.ptr, expected_scheme.len, uri.scheme.ptr, uri.scheme.len);

    struct aws_byte_cursor expected_authority =
        aws_byte_cursor_from_c_str("[2001:db8:85a3:8d3:1319:8a2e:370:7348%25en0]");
    ASSERT_BIN_ARRAYS_EQUALS(expected_authority.ptr, expected_authority.len, uri.authority.ptr, uri.authority.len);

    struct aws_byte_cursor expected_host = aws_byte_cursor_from_c_str("2001:db8:85a3:8d3:1319:8a2e:370:7348%25en0");
    ASSERT_BIN_ARRAYS_EQUALS(expected_host.ptr, expected_host.len, uri.host_name.ptr, uri.host_name.len);

    struct aws_byte_cursor expected_path = aws_byte_cursor_from_c_str("");
    ASSERT_BIN_ARRAYS_EQUALS(expected_path.ptr, expected_path.len, uri.path.ptr, uri.path.len);

    ASSERT_UINT_EQUALS(0U, uri.query_string.len);

    aws_uri_clean_up(&uri);
    return AWS_OP_SUCCESS;
}

AWS_TEST_CASE(uri_ipv6_no_port_parse, s_test_uri_ipv6_no_port_parse);

static int s_test_uri_invalid_scheme_parse(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;
    const char *str_uri =
        "https:/www.test.com:8443/path/to/resource?test1=value1&test%20space=value%20space&test2=value2&test2=value3";

    struct aws_byte_cursor uri_csr = aws_byte_cursor_from_c_str(str_uri);
    struct aws_uri uri;
    ASSERT_ERROR(AWS_ERROR_MALFORMED_INPUT_STRING, aws_uri_init_parse(&uri, allocator, &uri_csr));
    return AWS_OP_SUCCESS;
}

AWS_TEST_CASE(uri_invalid_scheme_parse, s_test_uri_invalid_scheme_parse);

static int s_test_uri_invalid_port_parse(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;
    const char *str_uri =
        "https://www.test.com:s8443/path/to/resource?test1=value1&test%20space=value%20space&test2=value2&test2=value3";

    struct aws_byte_cursor uri_csr = aws_byte_cursor_from_c_str(str_uri);
    struct aws_uri uri;
    ASSERT_ERROR(AWS_ERROR_MALFORMED_INPUT_STRING, aws_uri_init_parse(&uri, allocator, &uri_csr));
    return AWS_OP_SUCCESS;
}

AWS_TEST_CASE(uri_invalid_port_parse, s_test_uri_invalid_port_parse);

static int s_test_uri_port_too_large_parse(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;
    const char *str_uri = "https://www.test.com:4294967296/path/to/"
                          "resource?test1=value1&test%20space=value%20space&test2=value2&test2=value3";

    struct aws_byte_cursor uri_csr = aws_byte_cursor_from_c_str(str_uri);
    struct aws_uri uri;
    ASSERT_ERROR(AWS_ERROR_MALFORMED_INPUT_STRING, aws_uri_init_parse(&uri, allocator, &uri_csr));
    return AWS_OP_SUCCESS;
}

AWS_TEST_CASE(uri_port_too_large_parse, s_test_uri_port_too_large_parse);

static int s_test_uri_builder(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;
    const char *str_uri =
        "https://www.test.com:8443/path/to/resource?test1=value1&test%20space=value%20space&test2=value2&test2=value3";

    struct aws_byte_cursor uri_csr = aws_byte_cursor_from_c_str(str_uri);
    struct aws_uri uri;
    ASSERT_SUCCESS(aws_uri_init_parse(&uri, allocator, &uri_csr));

    struct aws_uri_param params[4];
    AWS_ZERO_ARRAY(params);

    struct aws_array_list params_list;
    aws_array_list_init_static(&params_list, &params, 4, sizeof(struct aws_uri_param));

    ASSERT_SUCCESS(aws_uri_query_string_params(&uri, &params_list));

    struct aws_uri_builder_options builder_args = {
        .scheme = uri.scheme,
        .path = uri.path,
        .host_name = uri.host_name,
        .port = uri.port,
        .query_params = &params_list,
    };

    struct aws_uri built_uri;
    ASSERT_SUCCESS(aws_uri_init_from_builder_options(&built_uri, allocator, &builder_args));

    struct aws_byte_cursor expected_scheme = aws_byte_cursor_from_c_str("https");
    ASSERT_BIN_ARRAYS_EQUALS(expected_scheme.ptr, expected_scheme.len, built_uri.scheme.ptr, built_uri.scheme.len);

    struct aws_byte_cursor expected_authority = aws_byte_cursor_from_c_str("www.test.com:8443");
    ASSERT_BIN_ARRAYS_EQUALS(
        expected_authority.ptr, expected_authority.len, built_uri.authority.ptr, built_uri.authority.len);

    struct aws_byte_cursor expected_host = aws_byte_cursor_from_c_str("www.test.com");
    ASSERT_BIN_ARRAYS_EQUALS(expected_host.ptr, expected_host.len, built_uri.host_name.ptr, built_uri.host_name.len);

    ASSERT_UINT_EQUALS(8443, built_uri.port);

    struct aws_byte_cursor expected_path = aws_byte_cursor_from_c_str("/path/to/resource");
    ASSERT_BIN_ARRAYS_EQUALS(expected_path.ptr, expected_path.len, built_uri.path.ptr, built_uri.path.len);

    struct aws_byte_cursor expected_query_str =
        aws_byte_cursor_from_c_str("test1=value1&test%20space=value%20space&test2=value2&test2=value3");
    ASSERT_BIN_ARRAYS_EQUALS(
        expected_query_str.ptr, expected_query_str.len, built_uri.query_string.ptr, built_uri.query_string.len);

    struct aws_byte_cursor expected_request_uri = aws_byte_cursor_from_c_str(
        "/path/to/resource?test1=value1&test%20space=value%20space&test2=value2&test2=value3");
    ASSERT_BIN_ARRAYS_EQUALS(
        expected_request_uri.ptr, expected_request_uri.len, built_uri.path_and_query.ptr, built_uri.path_and_query.len);

    aws_uri_clean_up(&uri);
    aws_uri_clean_up(&built_uri);
    return AWS_OP_SUCCESS;
}

AWS_TEST_CASE(uri_builder, s_test_uri_builder);

static int s_test_uri_builder_from_string(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;
    const char *str_uri =
        "https://www.test.com:8443/path/to/resource?test1=value1&test%20space=value%20space&test2=value2&test2=value3";

    struct aws_byte_cursor uri_csr = aws_byte_cursor_from_c_str(str_uri);
    struct aws_uri uri;
    ASSERT_SUCCESS(aws_uri_init_parse(&uri, allocator, &uri_csr));

    struct aws_uri_param params[4];
    AWS_ZERO_ARRAY(params);

    struct aws_byte_cursor query_string =
        aws_byte_cursor_from_c_str("test1=value1&test%20space=value%20space&test2=value2&test2=value3");

    struct aws_uri_builder_options builder_args = {
        .scheme = uri.scheme,
        .path = uri.path,
        .host_name = uri.host_name,
        .port = uri.port,
        .query_string = query_string,
    };

    struct aws_uri built_uri;
    ASSERT_SUCCESS(aws_uri_init_from_builder_options(&built_uri, allocator, &builder_args));

    struct aws_byte_cursor expected_scheme = aws_byte_cursor_from_c_str("https");
    ASSERT_BIN_ARRAYS_EQUALS(expected_scheme.ptr, expected_scheme.len, built_uri.scheme.ptr, built_uri.scheme.len);

    struct aws_byte_cursor expected_authority = aws_byte_cursor_from_c_str("www.test.com:8443");
    ASSERT_BIN_ARRAYS_EQUALS(
        expected_authority.ptr, expected_authority.len, built_uri.authority.ptr, built_uri.authority.len);

    struct aws_byte_cursor expected_host = aws_byte_cursor_from_c_str("www.test.com");
    ASSERT_BIN_ARRAYS_EQUALS(expected_host.ptr, expected_host.len, built_uri.host_name.ptr, built_uri.host_name.len);

    ASSERT_UINT_EQUALS(8443, built_uri.port);

    struct aws_byte_cursor expected_path = aws_byte_cursor_from_c_str("/path/to/resource");
    ASSERT_BIN_ARRAYS_EQUALS(expected_path.ptr, expected_path.len, built_uri.path.ptr, built_uri.path.len);

    ASSERT_BIN_ARRAYS_EQUALS(
        query_string.ptr, query_string.len, built_uri.query_string.ptr, built_uri.query_string.len);

    struct aws_byte_cursor expected_request_uri = aws_byte_cursor_from_c_str(
        "/path/to/resource?test1=value1&test%20space=value%20space&test2=value2&test2=value3");
    ASSERT_BIN_ARRAYS_EQUALS(
        expected_request_uri.ptr, expected_request_uri.len, built_uri.path_and_query.ptr, built_uri.path_and_query.len);

    aws_uri_clean_up(&uri);
    aws_uri_clean_up(&built_uri);
    return AWS_OP_SUCCESS;
}

AWS_TEST_CASE(uri_builder_from_string, s_test_uri_builder_from_string);

static int s_test_uri_encode_path_case(
    struct aws_allocator *allocator,
    const char *input,
    const char *expected_output) {
    struct aws_byte_buf encoding;
    ASSERT_SUCCESS(aws_byte_buf_init(&encoding, allocator, 100));

    struct aws_byte_cursor path_cursor = aws_byte_cursor_from_c_str(input);
    ASSERT_SUCCESS(aws_byte_buf_append_encoding_uri_path(&encoding, &path_cursor));

    struct aws_byte_cursor expected_path = aws_byte_cursor_from_c_str(expected_output);
    ASSERT_BIN_ARRAYS_EQUALS(encoding.buffer, encoding.len, expected_path.ptr, expected_path.len);

    aws_byte_buf_clean_up(&encoding);

    return AWS_OP_SUCCESS;
}

static int s_test_uri_encode_path_rfc3986(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;

    ASSERT_SUCCESS(s_test_uri_encode_path_case(allocator, "/path/1234/", "/path/1234/"));
    ASSERT_SUCCESS(s_test_uri_encode_path_case(
        allocator, "/abcdefghijklmnopqrstuvwxyz/1234567890/", "/abcdefghijklmnopqrstuvwxyz/1234567890/"));
    ASSERT_SUCCESS(s_test_uri_encode_path_case(
        allocator, "/ABCDEFGHIJKLMNOPQRSTUVWXYZ/1234567890/", "/ABCDEFGHIJKLMNOPQRSTUVWXYZ/1234567890/"));
    ASSERT_SUCCESS(s_test_uri_encode_path_case(
        allocator,
        "/ABCDEFGHIJKLMNOPQRSTUVWXYZ/_-~./$@&,:;=/",
        "/ABCDEFGHIJKLMNOPQRSTUVWXYZ/_-~./%24%40%26%2C%3A%3B%3D/"));
    ASSERT_SUCCESS(s_test_uri_encode_path_case(allocator, "/path/%^#! /", "/path/%25%5E%23%21%20/"));
    ASSERT_SUCCESS(s_test_uri_encode_path_case(allocator, "/path/ሴ", "/path/%E1%88%B4"));
    ASSERT_SUCCESS(s_test_uri_encode_path_case(
        allocator, "/path/\"'()*+<>[\\]`{|}/", "/path/%22%27%28%29%2A%2B%3C%3E%5B%5C%5D%60%7B%7C%7D/"));

    return AWS_OP_SUCCESS;
}

AWS_TEST_CASE(test_uri_encode_path_rfc3986, s_test_uri_encode_path_rfc3986);

static int s_test_uri_encode_param_case(
    struct aws_allocator *allocator,
    const char *input,
    const char *expected_output) {
    struct aws_byte_buf encoding;
    ASSERT_SUCCESS(aws_byte_buf_init(&encoding, allocator, 10));

    struct aws_byte_cursor path_cursor = aws_byte_cursor_from_c_str(input);
    ASSERT_SUCCESS(aws_byte_buf_append_encoding_uri_param(&encoding, &path_cursor));

    struct aws_byte_cursor expected_path = aws_byte_cursor_from_c_str(expected_output);
    ASSERT_BIN_ARRAYS_EQUALS(encoding.buffer, encoding.len, expected_path.ptr, expected_path.len);

    aws_byte_buf_clean_up(&encoding);

    return AWS_OP_SUCCESS;
}

static int s_test_uri_encode_query(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;
    (void)allocator;

    ASSERT_SUCCESS(s_test_uri_encode_param_case(
        allocator,
        "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz",
        "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz"));
    ASSERT_SUCCESS(s_test_uri_encode_param_case(allocator, "1234567890", "1234567890"));
    ASSERT_SUCCESS(s_test_uri_encode_param_case(allocator, "_~.-", "_~.-"));
    ASSERT_SUCCESS(s_test_uri_encode_param_case(allocator, "%^#! ", "%25%5E%23%21%20"));
    ASSERT_SUCCESS(s_test_uri_encode_param_case(allocator, "/$@&,:;=", "%2F%24%40%26%2C%3A%3B%3D"));
    ASSERT_SUCCESS(s_test_uri_encode_param_case(allocator, "ሴ", "%E1%88%B4"));
    ASSERT_SUCCESS(
        s_test_uri_encode_param_case(allocator, "\"'()*+<>[\\]`{|}", "%22%27%28%29%2A%2B%3C%3E%5B%5C%5D%60%7B%7C%7D"));

    return AWS_OP_SUCCESS;
}

AWS_TEST_CASE(test_uri_encode_query, s_test_uri_encode_query);

static int s_test_uri_decode_ok(struct aws_allocator *allocator, const char *input, const char *expected_output) {
    struct aws_byte_buf decoding;
    ASSERT_SUCCESS(aws_byte_buf_init(&decoding, allocator, 10));

    struct aws_byte_cursor input_cursor = aws_byte_cursor_from_c_str(input);
    ASSERT_SUCCESS(aws_byte_buf_append_decoding_uri(&decoding, &input_cursor));

    ASSERT_BIN_ARRAYS_EQUALS(expected_output, strlen(expected_output), decoding.buffer, decoding.len);

    aws_byte_buf_clean_up(&decoding);
    return AWS_OP_SUCCESS;
}

static int s_test_uri_decode_err(struct aws_allocator *allocator, const char *input) {
    struct aws_byte_buf decoding;
    ASSERT_SUCCESS(aws_byte_buf_init(&decoding, allocator, 10));

    struct aws_byte_cursor input_cursor = aws_byte_cursor_from_c_str(input);
    ASSERT_ERROR(AWS_ERROR_MALFORMED_INPUT_STRING, aws_byte_buf_append_decoding_uri(&decoding, &input_cursor));

    aws_byte_buf_clean_up(&decoding);
    return AWS_OP_SUCCESS;
}

static int s_test_uri_roundtrip(struct aws_allocator *allocator, const char *input) {
    struct aws_byte_cursor input_cursor = aws_byte_cursor_from_c_str(input);

    struct aws_byte_buf encoding;
    ASSERT_SUCCESS(aws_byte_buf_init(&encoding, allocator, 10));

    struct aws_byte_buf decoding;
    ASSERT_SUCCESS(aws_byte_buf_init(&decoding, allocator, 10));

    /* test param roundtrip encode/decode */
    ASSERT_SUCCESS(aws_byte_buf_append_encoding_uri_param(&encoding, &input_cursor));

    struct aws_byte_cursor encoding_cursor = aws_byte_cursor_from_buf(&encoding);
    ASSERT_SUCCESS(aws_byte_buf_append_decoding_uri(&decoding, &encoding_cursor));

    ASSERT_BIN_ARRAYS_EQUALS(input, strlen(input), decoding.buffer, decoding.len);

    /* test path roundtrip encode/decode */
    aws_byte_buf_reset(&encoding, false);
    aws_byte_buf_reset(&decoding, false);

    ASSERT_SUCCESS(aws_byte_buf_append_encoding_uri_path(&encoding, &input_cursor));

    encoding_cursor = aws_byte_cursor_from_buf(&encoding);
    ASSERT_SUCCESS(aws_byte_buf_append_decoding_uri(&decoding, &encoding_cursor));

    ASSERT_BIN_ARRAYS_EQUALS(input, strlen(input), decoding.buffer, decoding.len);

    aws_byte_buf_clean_up(&encoding);
    aws_byte_buf_clean_up(&decoding);
    return AWS_OP_SUCCESS;
}

static int s_test_uri_decode(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;

    /* test against expected */
    ASSERT_SUCCESS(s_test_uri_decode_ok(allocator, "", ""));
    ASSERT_SUCCESS(s_test_uri_decode_ok(allocator, "abc123", "abc123"));
    ASSERT_SUCCESS(s_test_uri_decode_ok(allocator, "%20", " "));
    ASSERT_SUCCESS(s_test_uri_decode_ok(allocator, "%E1%88%B4", "ሴ"));
    ASSERT_SUCCESS(s_test_uri_decode_ok(allocator, "%e1%88%b4", "ሴ"));
    ASSERT_SUCCESS(s_test_uri_decode_ok(allocator, "%2520", "%20"));
    ASSERT_SUCCESS(s_test_uri_decode_ok(allocator, "ሴ", "ሴ")); /* odd input should just pass through */
    ASSERT_SUCCESS(s_test_uri_decode_ok(
        allocator,
        "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz", /* long enough to resize output buffer */
        "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz"));

    /* these should fail */
    ASSERT_SUCCESS(s_test_uri_decode_err(allocator, "%"));
    ASSERT_SUCCESS(s_test_uri_decode_err(allocator, "%2"));
    ASSERT_SUCCESS(s_test_uri_decode_err(allocator, "%%20"));
    ASSERT_SUCCESS(s_test_uri_decode_err(allocator, "%fg"));
    ASSERT_SUCCESS(s_test_uri_decode_err(allocator, "%gf"));

    /* Test roundtrip encoding and decoding. Results should match original input */
    ASSERT_SUCCESS(s_test_uri_roundtrip(allocator, ""));
    ASSERT_SUCCESS(s_test_uri_roundtrip(allocator, "abc123"));
    ASSERT_SUCCESS(s_test_uri_roundtrip(allocator, "a + b"));
    ASSERT_SUCCESS(s_test_uri_roundtrip(allocator, "ሴ"));

    /* do roundtrip test against every possible value (except 0 because helper functions use c-strings) */
    uint8_t every_value[256];
    for (size_t i = 0; i < 255; ++i) {
        every_value[i] = (uint8_t)(i + 1);
    }
    every_value[255] = 0;
    ASSERT_SUCCESS(s_test_uri_roundtrip(allocator, (const char *)every_value));

    return AWS_OP_SUCCESS;
}
AWS_TEST_CASE(test_uri_decode, s_test_uri_decode);
