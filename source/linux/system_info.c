
#include <aws/common/private/system_info_priv.h>
#include <aws/common/file.h>

int aws_system_environment_load_platform_impl(struct aws_system_environment *env) {
    aws_byte_buf_init_from_file(&env->virtualization_vendor, env->allocator, "/sys/devices/virtual/dmi/id/sys_vendor");
    aws_byte_buf_init_from_file(&env->product_name, env->allocator, "/sys/devices/virtual/dmi/id/product_name");

    return AWS_OP_SUCCESS;
}

void aws_system_environment_destroy_platform_impl(struct aws_system_environment *env) {
    aws_byte_buf_clean_up(&env->virtualization_vendor);
    aws_byte_buf_clean_up(&env->product_name);
}

