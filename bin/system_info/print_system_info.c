


#include <aws/common/system_info.h>
#include <aws/common/byte_buf.h>

int main(void) {
    struct aws_allocator *allocator = aws_default_allocator();
    struct aws_system_environment *env = aws_system_environment_load(allocator);

    fprintf(stdout, "crt-detected env: {\n");

    struct aws_byte_cursor virtualization_vendor = aws_system_environment_get_virtualization_vendor(env);
    fprintf(stdout, "  'virtualization vendor': '" PRInSTR "'\n", (int)virtualization_vendor.len, virtualization_vendor.ptr);
    fprintf(stdout, "  'number of processors': '%lu'\n", (unsigned long)aws_system_environment_get_processor_count(env));
    size_t numa_nodes = aws_system_environment_get_cpu_group_count(env);

    if (numa_nodes > 1) {
        fprintf(stdout, "  'numa architecture': 'true'\n");
        fprintf(stdout, "  'number of numa nodes': '%lu'\n", (unsigned long)numa_nodes);
    } else {
        fprintf(stdout, "  'numa architecture': 'false'\n");
    }

    fprintf(stdout, "}\n");
    aws_system_environment_destroy(env);
    return 0;
}
