use aws_crt_c_flags::CRTModuleBuildInfo;
use std::borrow::{Borrow, BorrowMut};
use std::path::Path;

fn load_compiler_configuration(build_config: &mut CRTModuleBuildInfo) {
    let mut config_file_str: String = "#ifndef AWS_COMMON_CONFIG_H
#define AWS_COMMON_CONFIG_H

/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

/*
 * This header exposes compiler feature test results determined during cmake
 * configure time to inline function implementations. The macros defined here
 * should be considered to be an implementation detail, and can change at any
 * time.
 */\n"
        .to_string();

    build_config.add_public_define("AWS_NO_STATIC_IMPL", "1");
    config_file_str = format!("{}#define AWS_NO_STATIC_IMPL 1\n", config_file_str);

    #[target_feature(enable = "avx2")]
    {
        build_config.add_private_define("HAVE_AVX2_INTRINSICS", "1");
        build_config.add_private_define("HAVE_MM256_EXTRACT_EPI64", "1");

        if build_config.get_toolchain().get_compiler().is_like_msvc() {
            build_config.add_public_cflag("/arch:AVX2");
        } else {
            build_config
                .add_public_cflag("-mavx")
                .add_public_cflag("-mavx2");
        }
    }

    if build_config
        .try_compile(
            "#include <stdbool.h>
        bool foo(int a, int b, int *c) {
            return __builtin_mul_overflow(a, b, c);
        }

        int main() {
            int out;

            if (foo(1, 2, &out)) {
                return 0;
            }
            return 0;
        }",
        )
        .is_ok()
    {
        build_config.add_private_define("AWS_HAVE_GCC_OVERFLOW_MATH_EXTENSIONS", "1");
        config_file_str = format!(
            "{}#define AWS_HAVE_GCC_OVERFLOW_MATH_EXTENSIONS 1\n",
            config_file_str
        );
    }

    if build_config
        .try_compile(
            "int main() {
            int foo = 42;
            _mulx_u32(1, 2, &foo);
            return foo != 2;
        }",
        )
        .is_ok()
    {
        build_config.add_public_define("AWS_HAVE_MSVC_MULX", "1");
    }

    if build_config
        .try_compile(
            "#include <Windows.h>
         #if WINAPI_FAMILY_PARTITION(WINAPI_PARTITION_DESKTOP)
        int main() {
            return 0;
        }
        #else
        it's not windows desktop
        #endif",
        )
        .is_ok()
    {
        build_config.add_public_define("AWS_HAVE_WINAPI_DESKTOP", "1");
        config_file_str = format!("{}#define AWS_HAVE_WINAPI_DESKTOP 1\n", config_file_str);
    }

    #[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
    {
        build_config.add_public_define("AWS_ARCH_INTEL", "1");
        config_file_str = format!("{}#define AWS_ARCH_INTEL 1\n", config_file_str);
    }

    #[cfg(target_arch = "aarch64")]
    {
        build_config.add_public_define("AWS_ARCH_ARM64", "1");
        config_file_str = format!("{}#define AWS_ARCH_ARM64 1\n", config_file_str);
    }

    #[cfg(target_arch = "arm")]
    {
        build_config.add_public_define("AWS_ARCH_ARM32", "1");
        config_file_str = format!("{}#define AWS_ARCH_ARM32 1\n", config_file_str);
    }

    if build_config
        .try_compile(
            "int main() {
        int foo = 42, bar = 24;
        __asm__ __volatile__(\"\":\"=r\"(foo):\"r\"(bar):\"memory\");\
        return 0;\
        }",
        )
        .is_ok()
    {
        build_config.add_private_define("AWS_HAVE_GCC_INLINE_ASM", "1");
        config_file_str = format!("{}#define AWS_HAVE_GCC_INLINE_ASM 1\n", config_file_str);
    }

    if build_config
        .try_compile(
            "#include <sys/auxv.h>
        int main() {
        #ifdef __linux__
            getauxval(AT_HWCAP);
            getauxval(AT_HWCAP2);
        #endif
        return 0;
        }",
        )
        .is_ok()
    {
        build_config.add_private_define("AWS_HAVE_AUXV", "1");
        config_file_str = format!("{}#define AWS_HAVE_AUXV 1\n", config_file_str);
    }

    if build_config
        .try_compile(
            "#include <execinfo.h>
        int main() {
            return 0;
        }",
        )
        .is_ok()
    {
        build_config.add_private_define("AWS_HAVE_EXECINFO", "1");
        config_file_str = format!("{}#define AWS_HAVE_EXECINFO 1\n", config_file_str);
    }

    if build_config
        .try_compile(
            "#include <unistd.h>
        int main() {
            sysconf(_SC_NPROCESSORS_ONLN);
            return 0;
        }",
        )
        .is_ok()
    {
        build_config.add_private_define("HAVE_SYSCONF", "1");
        config_file_str = format!("{}#define HAVE_SYSCONF 1\n", config_file_str);
    }
    config_file_str = format!("{}#endif\n", config_file_str);
    let output_path = Path::new("include/aws/common/config.h");
    build_config
        .write_generated_file_to_output_path(config_file_str.to_string().borrow(), output_path);
}
fn main() {
    let mut build_info = CRTModuleBuildInfo::new("aws-c-common");
    load_compiler_configuration(build_info.borrow_mut());
    let include_path = Path::new("../../include/aws");
    build_info.add_include_dir_and_copy_to_build_tree(include_path);

    build_info
        .add_file_to_build(Path::new("../../source/allocator.c"))
        .add_file_to_build(Path::new("../../source/allocator_sba.c"))
        .add_file_to_build(Path::new("../../source/array_list.c"))
        .add_file_to_build(Path::new("../../source/assert.c"))
        .add_file_to_build(Path::new("../../source/atomics.c"))
        .add_file_to_build(Path::new("../../source/byte_buf.c"))
        .add_file_to_build(Path::new("../../source/cache.c"))
        .add_file_to_build(Path::new("../../source/clock.c"))
        .add_file_to_build(Path::new("../../source/command_line_parser.c"))
        .add_file_to_build(Path::new("../../source/common.c"))
        .add_file_to_build(Path::new("../../source/condition_variable.c"))
        .add_file_to_build(Path::new("../../source/date_time.c"))
        .add_file_to_build(Path::new("../../source/device_random.c"))
        .add_file_to_build(Path::new("../../source/encoding.c"))
        .add_file_to_build(Path::new("../../source/error.c"))
        .add_file_to_build(Path::new("../../source/fifo_cache.c"))
        .add_file_to_build(Path::new("../../source/hash_table.c"))
        .add_file_to_build(Path::new("../../source/lifo_cache.c"))
        .add_file_to_build(Path::new("../../source/linked_list.c"))
        .add_file_to_build(Path::new("../../source/linked_hash_table.c"))
        .add_file_to_build(Path::new("../../source/log_channel.c"))
        .add_file_to_build(Path::new("../../source/log_formatter.c"))
        .add_file_to_build(Path::new("../../source/log_writer.c"))
        .add_file_to_build(Path::new("../../source/logging.c"))
        .add_file_to_build(Path::new("../../source/lru_cache.c"))
        .add_file_to_build(Path::new("../../source/math.c"))
        .add_file_to_build(Path::new("../../source/memtrace.c"))
        .add_file_to_build(Path::new("../../source/priority_queue.c"))
        .add_file_to_build(Path::new("../../source/process_common.c"))
        .add_file_to_build(Path::new("../../source/ref_count.c"))
        .add_file_to_build(Path::new("../../source/resource_name.c"))
        .add_file_to_build(Path::new("../../source/ring_buffer.c"))
        .add_file_to_build(Path::new("../../source/statistics.c"))
        .add_file_to_build(Path::new("../../source/string.c"))
        .add_file_to_build(Path::new("../../source/task_scheduler.c"))
        .add_file_to_build(Path::new("../../source/thread_scheduler.c"))
        .add_file_to_build(Path::new("../../source/thread_shared.c"))
        .add_file_to_build(Path::new("../../source/uuid.c"))
        .add_file_to_build(Path::new("../../source/xml_parser.c"));

    #[cfg(windows)]
    {
        build_info
            .add_file_to_build(Path::new("../../source/windows/clock.c"))
            .add_file_to_build(Path::new("../../source/windows/condition_variable.c"))
            .add_file_to_build(Path::new("../../source/windows/device_random.c"))
            .add_file_to_build(Path::new("../../source/windows/environment.c"))
            .add_file_to_build(Path::new("../../source/windows/file.c"))
            .add_file_to_build(Path::new("../../source/windows/mutex.c"))
            .add_file_to_build(Path::new("../../source/windows/process.c"))
            .add_file_to_build(Path::new("../../source/windows/rw_lock.c"))
            .add_file_to_build(Path::new("../../source/windows/system_info.c"))
            .add_file_to_build(Path::new("../../source/windows/thread.c"))
            .add_file_to_build(Path::new("../../source/windows/time.c"));

        #[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
        {
            if build_info.get_toolchain().get_compiler().is_like_msvc() {
                build_info.add_file_to_build(Path::new("../../source/arch/intel/msvc/cpuid.c"));
            }
        }

        build_info
            .add_link_target("Kernel32")
            .add_link_target("BCrypt")
            .add_link_target("Ws2_32");
    }

    #[cfg(not(Windows))]
    {
        build_info
            .add_file_to_build(Path::new("../../source/posix/clock.c"))
            .add_file_to_build(Path::new("../../source/posix/condition_variable.c"))
            .add_file_to_build(Path::new("../../source/posix/device_random.c"))
            .add_file_to_build(Path::new("../../source/posix/environment.c"))
            .add_file_to_build(Path::new("../../source/posix/file.c"))
            .add_file_to_build(Path::new("../../source/posix/mutex.c"))
            .add_file_to_build(Path::new("../../source/posix/process.c"))
            .add_file_to_build(Path::new("../../source/posix/rw_lock.c"))
            .add_file_to_build(Path::new("../../source/posix/system_info.c"))
            .add_file_to_build(Path::new("../../source/posix/thread.c"))
            .add_file_to_build(Path::new("../../source/posix/time.c"));

        #[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
        {
            build_info.add_file_to_build(Path::new("../../source/arch/intel/asm/cpuid.c"));
        }

        build_info.add_link_target("dl").add_link_target("pthread");

        #[cfg(target_os = "macos")]
        {
            build_info.add_link_target("framework=CoreFoundation");
            build_info.add_private_define("AWS_AFFINITY_METHOD", "AWS_AFFINITY_METHOD_NONE");
        }

        #[cfg(target_os = "linux")]
        {
            build_info.add_link_target("rt");
        }

        #[cfg(any(target_os = "freebsd", target_os = "netbsd", target_os = "openbsd"))]
        {
            build_info
                .add_link_target("m")
                .add_link_target("thr")
                .add_link_target("execinfo");
        }

        #[cfg(any(
            target_os = "freebsd",
            target_os = "netbsd",
            target_os = "openbsd",
            target_env = "musl"
        ))]
        {
            build_info.add_private_define("AWS_AFFINITY_METHOD", "AWS_AFFINITY_METHOD_PTHREAD")
        }

        #[cfg(not(any(
            target_os = "freebsd",
            target_os = "netbsd",
            target_os = "openbsd",
            target_env = "musl",
            target_os = "macos"
        )))]
        {
            build_info.add_private_define("AWS_AFFINITY_METHOD", "AWS_AFFINITY_METHOD_PTHREAD_ATTR")
        }

        build_info.add_private_define("_GNU_SOURCE", "1");
    }

    #[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
    {
        build_info
            .add_file_to_build(Path::new("../../source/arch/intel/cpuid.c"))
            .add_file_to_build(Path::new("../../source/arch/intel/encoding_avx2.c"));
    }

    #[cfg(any(target_arch = "aarch64", target_arch = "arm"))]
    {
        build_info.add_file_to_build(Path::new("../../source/arch/arm/cpuid.c"))
    }

    #[cfg(not(any(
        target_arch = "x86",
        target_arch = "x86_64",
        target_arch = "aarch64",
        target_arch = "arm"
    )))]
    {
        build_info.add_file_to_build(Path::new("../../source/arch/generic/cpuid.c"));
    }

    build_info.run_build();
}
