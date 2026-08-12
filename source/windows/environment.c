/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/common/environment.h>
#include <aws/common/string.h>

#include <stdlib.h>

struct aws_string *aws_get_env(struct aws_allocator *allocator, const char *name) {
#ifdef _MSC_VER
    /*
     * On Windows, environment variables are natively stored as wide (UTF-16)
     * strings. The narrow getenv()/_dupenv_s() APIs return values in the active
     * ANSI code page, which is a lossy compatibility layer. Downstream code
     * (aws_fopen_safe) assumes all strings are UTF-8, so reading through the
     * narrow API produces encoding mismatches for non-ASCII values.
     *
     * We use _wdupenv_s to read the authoritative wide value, then convert to
     * UTF-8 for consistent handling throughout the SDK.
     */

    /* Convert variable name to wide (env var names are ASCII, which is valid UTF-8) */
    struct aws_byte_cursor name_cursor = aws_byte_cursor_from_c_str(name);
    struct aws_wstring *w_name = aws_string_convert_to_wchar_from_byte_cursor(allocator, &name_cursor);
    if (!w_name) {
        return NULL;
    }

    /* Read value as wide characters using _wdupenv_s */
    wchar_t *w_value = NULL;
    size_t w_value_len = 0;
    errno_t err = _wdupenv_s(&w_value, &w_value_len, aws_wstring_c_str(w_name));
    aws_wstring_destroy(w_name);

    if (err != 0 || w_value == NULL || w_value_len == 0) {
        free(w_value);
        return NULL;
    }

    /* Convert wide value to UTF-8 */
    struct aws_string *result = aws_string_convert_from_wchar_c_str(allocator, w_value);
    free(w_value);

    return result;
#else
    const char *value = getenv(name);

    if (value == NULL) {
        return NULL;
    }

    return aws_string_new_from_c_str(allocator, value);
#endif
}

struct aws_string *aws_get_env_nonempty(struct aws_allocator *allocator, const char *name) {
    struct aws_string *value = aws_get_env(allocator, name);
    if (value == NULL) {
        return NULL;
    }
    if (value->len == 0) {
        aws_string_destroy(value);
        return NULL;
    }
    return value;
}

int aws_get_environment_value(
    struct aws_allocator *allocator,
    const struct aws_string *variable_name,
    struct aws_string **value_out) {

    *value_out = aws_get_env(allocator, aws_string_c_str(variable_name));

    return AWS_OP_SUCCESS;
}

int aws_set_environment_value(const struct aws_string *variable_name, const struct aws_string *value) {
    if (_putenv_s(aws_string_c_str(variable_name), aws_string_c_str(value)) != 0) {
        return aws_raise_error(AWS_ERROR_ENVIRONMENT_SET);
    }

    return AWS_OP_SUCCESS;
}

AWS_STATIC_STRING_FROM_LITERAL(s_empty_string, "");

int aws_unset_environment_value(const struct aws_string *variable_name) {
    if (_putenv_s(aws_string_c_str(variable_name), aws_string_c_str(s_empty_string)) != 0) {
        return aws_raise_error(AWS_ERROR_ENVIRONMENT_UNSET);
    }

    return AWS_OP_SUCCESS;
}
