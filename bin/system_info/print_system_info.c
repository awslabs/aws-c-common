

#include <aws/common/byte_buf.h>
#include <aws/common/logging.h>
#include <aws/common/system_info.h>
#include <aws/common/cpuid.h>

int main(void) {
    struct aws_allocator *allocator = aws_default_allocator();
    aws_common_library_init(allocator);
    struct aws_logger_standard_options options = {
        .file = stderr,
        .level = AWS_LOG_LEVEL_TRACE,
    };

    struct aws_logger logger;
    aws_logger_init_standard(&logger, allocator, &options);
    aws_logger_set(&logger);

    struct aws_system_environment *env = aws_system_environment_load(allocator);

    fprintf(stdout, "crt-detected env: {\n");

    struct aws_byte_cursor virtualization_vendor = aws_system_environment_get_virtualization_vendor(env);
    fprintf(
        stdout,
        "  'virtualization vendor': '" PRInSTR "',\n",
        (int)virtualization_vendor.len,
        virtualization_vendor.ptr);
    struct aws_byte_cursor product_name = aws_system_environment_get_virtualization_product_name(env);
    fprintf(stdout, "  'product name': '" PRInSTR "',\n", (int)product_name.len, product_name.ptr);
    fprintf(
        stdout, "  'number of processors': '%lu',\n", (unsigned long)aws_system_environment_get_processor_count(env));
    size_t numa_nodes = aws_system_environment_get_cpu_group_count(env);

    if (numa_nodes > 1) {
        fprintf(stdout, "  'numa architecture': 'true',\n");
        fprintf(stdout, "  'number of numa nodes': '%lu'\n", (unsigned long)numa_nodes);
    } else {
        fprintf(stdout, "  'numa architecture': 'false'\n");
    }

    fprintf(stdout, "   'cpu_capabilities': {\n");
    fprintf(stdout, "       'arm_crc': %s,\n", aws_cpu_has_feature(AWS_CPU_FEATURE_ARM_CRC) ? "true" : "false");
    fprintf(stdout, "       'arm_pmull': %s,\n", aws_cpu_has_feature(AWS_CPU_FEATURE_ARM_PMULL) ? "true" : "false");
    fprintf(stdout, "       'arm_crypto': %s,\n", aws_cpu_has_feature(AWS_CPU_FEATURE_ARM_CRYPTO) ? "true" : "false");
    fprintf(stdout, "       'amd_sse4_1': %s,\n", aws_cpu_has_feature(AWS_CPU_FEATURE_SSE_4_1) ? "true" : "false");
    fprintf(stdout, "       'amd_sse4_2': %s,\n", aws_cpu_has_feature(AWS_CPU_FEATURE_SSE_4_2) ? "true" : "false");
    fprintf(stdout, "       'amd_clmul': %s,\n", aws_cpu_has_feature(AWS_CPU_FEATURE_CLMUL) ? "true" : "false");
    fprintf(stdout, "       'amd_vpclmulqdq': %s,\n", aws_cpu_has_feature(AWS_CPU_FEATURE_VPCLMULQDQ) ? "true" : "false");
    fprintf(stdout, "       'amd_avx2': %s,\n", aws_cpu_has_feature(AWS_CPU_FEATURE_AVX2) ? "true" : "false");
    fprintf(stdout, "       'amd_avx512': %s,\n", aws_cpu_has_feature(AWS_CPU_FEATURE_AVX512) ? "true" : "false");
    fprintf(stdout, "       'amd_bmi2': %s\n", aws_cpu_has_feature(AWS_CPU_FEATURE_BMI2) ? "true" : "false");
    fprintf(stdout, "   }\n");

    fprintf(stdout, "}\n");
    aws_system_environment_release(env);
    aws_logger_clean_up(&logger);

    aws_common_library_clean_up();
    return 0;
}
