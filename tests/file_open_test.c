/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */
#include <aws/common/file_open.h>

#include <aws/testing/aws_test_harness.h>

static int s_aws_fopen_unicode_test_fn(struct aws_allocator *allocator, void *ctx) {
    (void)allocator;
    (void)ctx;

    wchar_t w_file_path[] = L"C:\\Users\\ting-\\Desktop\\project\\aws-c-common\\Åsample.txt";
    char I_don[] = "Schöne";
    char I_don_2[] = "Schone";
    printf("%s \n", I_don);
    printf("%d %d \n", (int)strlen(I_don), (int)strlen(I_don_2));
    // wchar_t file_path[] = L"Åsample.txt";
    // uint8_t *binary = (uint8_t *)file_path;
    // printf("%x %x\n", binary[0], binary[1]);
    // uint8_t temp = binary[1];
    // binary[1] = binary[0];
    // binary[0] = temp;
    // wchar_t *another_path = (wchar_t *)binary;
    // FILE *file = aws_fopen(file_path, "w+");
    FILE *file;
    if (_wfopen_s(&file, w_file_path, L"r")) {
        return AWS_OP_ERR;
    }
    // if (fopen_s(&file, file_path, "w+")) {
    //     return AWS_OP_ERR;
    // }
    fclose(file);
    return AWS_OP_SUCCESS;
}

AWS_TEST_CASE(aws_fopen_unicode_test, s_aws_fopen_unicode_test_fn)
