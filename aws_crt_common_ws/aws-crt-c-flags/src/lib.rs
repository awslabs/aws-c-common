use cc::Build;
use fs_extra;
use fs_extra::dir::CopyOptions;
use gag::Gag;
use serde::{Deserialize, Serialize};
use serde_json::Result;
use std::borrow::BorrowMut;
use std::env;
use std::fs;
use std::fs::File;
use std::io::{Read, Write};
use std::path::Path;
use std::path::PathBuf;

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct CRTModuleBuildInfo {
    crt_module_name: String,
    crt_module_deps: Vec<CRTModuleBuildInfo>,
    #[serde(skip_serializing, skip_deserializing)]
    private_cflags: Vec<String>,
    public_cflags: Vec<String>,
    #[serde(skip_serializing, skip_deserializing)]
    private_defines: Vec<(String, String)>,
    public_defines: Vec<(String, String)>,
    link_targets: Vec<String>,
    shared_lib: bool,
    lib_name: String,
    linker_path: Option<PathBuf>,
    #[serde(skip_serializing, skip_deserializing)]
    private_include_dirs: Vec<PathBuf>,
    public_include_dirs: Vec<PathBuf>,
    #[serde(skip_serializing, skip_deserializing)]
    build_toolchain: Build,
}

pub enum HeaderType {
    Private,
    Public,
}

impl CRTModuleBuildInfo {
    /// Creates a new instance of CRTModuleBuildInfo.
    /// # Arguments
    ///
    /// * `module_name` - Name of the module you want to build. This name will be used to identify
    ///                   build state across crates. We recommend you name it your sys crate name.
    ///                   For example: aws_crt_common_sys, aws_crt_http_sys etc...
    ///
    /// # Examples
    ///
    /// ```should_panic
    /// use aws_crt_c_flags::{CRTModuleBuildInfo};
    /// let build_info = CRTModuleBuildInfo::new("aws_crt_common_sys");
    /// ```
    pub fn new(module_name: &str) -> CRTModuleBuildInfo {
        CRTModuleBuildInfo {
            crt_module_name: module_name.parse().unwrap(),
            crt_module_deps: vec![],
            private_cflags: vec![],
            public_cflags: vec![],
            private_defines: vec![],
            public_defines: vec![],
            link_targets: vec![],
            shared_lib: false,
            lib_name: module_name.parse().unwrap(),
            linker_path: Option::from(PathBuf::from(env::var_os("OUT_DIR").unwrap())),
            private_include_dirs: vec![],
            public_include_dirs: vec![],
            build_toolchain: Build::new(),
        }
    }

    fn get_configuration_file(module_name: &str) -> File {
        let target_dir = env::var("OUT_DIR");
        let file_name = format!(
            "{}/CRT_MODULE_{}_BUILD_CFG",
            target_dir.expect("cargo env variable OUT_DIR isn't set"),
            module_name
        );

        if let Ok(file_open_res) = File::open(Path::new(file_name.as_str())) {
            return file_open_res;
        } else {
            return File::create(Path::new(file_name.as_str()))
                .expect("crt module metadata file creation failed!");
        }
    }

    /// Declares other aws crt modules to have your sys package depend on. This is used for transitively
    /// passing linker arguments and c-flags between different crates' builds of their sys modules.
    ///
    /// # Arguments
    ///
    /// * `dependency` - name of the crt sys crate you want to link your sys crate against. So for example,
    ///                  if you're building aws-checksums, your sys crate would be aws_crt_checksums_sys, and you
    ///                  would declare a dependency here on aws_crt_common_sys.
    ///
    /// # Examples
    /// ```should_panic
    /// use aws_crt_c_flags::{CRTModuleBuildInfo};
    /// let mut build_info = CRTModuleBuildInfo::new("aws_crt_checksums_sys");
    /// build_info.module_dependency("aws_crt_common_sys");
    /// ```
    pub fn module_dependency(&mut self, dependency: &str) -> &mut CRTModuleBuildInfo {
        let mut crt_module_file_res = CRTModuleBuildInfo::get_configuration_file(dependency);
        let mut crt_module_read_res = String::new();
        crt_module_file_res
            .read_to_string(crt_module_read_res.borrow_mut())
            .expect("configuration file read failed!");

        let parse_res: Result<CRTModuleBuildInfo> =
            serde_json::from_str(crt_module_read_res.as_str());

        if let Ok(parse_res) = parse_res {
            self.crt_module_deps.push(parse_res);
            return self;
        }
        panic!("Module: `{}` does not appear to be a part of your dependency chain. Alternatively, the dependencies build script does not call CRTModuleBuildInfo::run_build() correctly", dependency);
    }

    /// Adds a c-flag to your build, and guarantees that when another module calls add_module_dependency()
    /// on the module_name you used in ::new(), it will be transitively applied to their build.
    ///
    /// # Arguments
    ///
    /// * `c_flag` - compiler flag to apply to the build. Example `-fPIC`
    ///
    /// # Examples
    /// ```should_panic
    /// use aws_crt_c_flags::{CRTModuleBuildInfo};
    /// let mut build_info = CRTModuleBuildInfo::new("aws_crt_common_sys");
    /// build_info.public_cflag("-fPIC");
    /// ```
    pub fn public_cflag(&mut self, c_flag: &str) -> &mut CRTModuleBuildInfo {
        self.public_cflags.push(c_flag.parse().unwrap());
        self
    }

    /// Adds a c-flag to your build, this flag will only apply to the current building module and
    /// will not be transitively reflected to other modules' builds.
    ///
    /// # Arguments
    ///
    /// * `c_flag` - compiler flag to apply to the build. Example `-fPIC`
    ///
    /// # Examples
    /// ```should_panic
    /// use aws_crt_c_flags::{CRTModuleBuildInfo};
    /// let mut build_info = CRTModuleBuildInfo::new("aws_crt_common_sys");
    /// build_info.private_cflag("-Wall");
    /// ```
    pub fn private_cflag(&mut self, c_flag: &str) -> &mut CRTModuleBuildInfo {
        self.private_cflags.push(c_flag.parse().unwrap());
        self
    }

    /// Adds a definition to your build, this flag will only apply to the current building module and
    /// will not be transitively reflected to other modules' builds.
    ///
    /// # Arguments
    ///
    /// * `key` - definition name
    /// * `val` - definition value
    ///
    /// this has the effect of writing #define [key] [value] inside your compilation units.
    ///
    /// # Examples
    /// ```should_panic
    /// use aws_crt_c_flags::{CRTModuleBuildInfo};
    /// let mut build_info = CRTModuleBuildInfo::new("aws_crt_common_sys");
    /// build_info.private_define("MY_DEFINE", "MY_DEFINE_VALUE");
    /// ```
    pub fn private_define(&mut self, key: &str, val: &str) -> &mut CRTModuleBuildInfo {
        self.private_defines
            .push((key.parse().unwrap(), val.parse().unwrap()));
        self
    }

    /// Adds a definition to your build and guarantees that when another module calls add_module_dependency()
    /// on the module_name you used in ::new(), it will be transitively applied to their build.
    ///
    /// # Arguments
    ///
    /// * `key` - definition name
    /// * `val` - definition value
    ///
    /// this has the effect of writing #define [key] [value] inside your compilation units.
    ///
    /// # Examples
    /// ```should_panic
    /// use aws_crt_c_flags::{CRTModuleBuildInfo};
    /// let mut build_info = CRTModuleBuildInfo::new("aws_crt_common_sys");
    /// build_info.public_define("MY_DEFINE", "MY_DEFINE_VALUE");
    /// ```
    pub fn public_define(&mut self, key: &str, val: &str) -> &mut CRTModuleBuildInfo {
        self.public_defines
            .push((key.parse().unwrap(), val.parse().unwrap()));
        self
    }

    /// Adds a library to the linker line. Formatting for things like framework-vs-system lib are the responsibility
    /// of the caller. All link targets are transitively passed to module consumers.
    ///
    /// # Arguments
    ///
    /// * `l_flag` - Linker target. Example: "curl", "Kernel32", "framework=CoreFoundation"
    ///
    /// # Examples
    /// ```should_panic
    /// use aws_crt_c_flags::{CRTModuleBuildInfo};
    /// let mut build_info = CRTModuleBuildInfo::new("aws_crt_common_sys");
    /// build_info.link_target("crypto")
    ///     .link_target("framework=Security");
    /// ```
    pub fn link_target(&mut self, l_flag: &str) -> &mut CRTModuleBuildInfo {
        self.link_targets.push(l_flag.parse().unwrap());
        self
    }

    /// Makes this module build as a shared library. The default is static.
    pub fn make_shared_lib(&mut self) -> &mut CRTModuleBuildInfo {
        self.shared_lib = true;
        self
    }

    /// Sets the linker search path. Currently this is unused, but if you were to be using this
    /// module to link against a library built via. something other than cargo, you'd use this to do so.
    /// The default is the cargo build output directory.
    ///
    /// # Arguments
    ///
    /// * `path` - File system path to where to find libraries to link against (e.g. /usr/lib)
    ///
    /// # Examples
    /// ```should_panic
    /// use aws_crt_c_flags::{CRTModuleBuildInfo};
    /// use std::path::Path;
    /// let mut build_info = CRTModuleBuildInfo::new("aws_crt_common_sys");
    /// build_info.linker_search_path(Path::new("/opt/where/i/installed/my/manually/built/libcrypto/lib"))
    ///     .link_target("crypto");
    /// ```
    pub fn linker_search_path(&mut self, path: &Path) -> &mut CRTModuleBuildInfo {
        self.linker_path = Some(path.to_path_buf());
        self
    }

    /// adds an additional include directory to your module build. This is mainly useful only
    /// if you're using a 3rd party library, not built by this library, and you need the compiler
    /// to fine the header files.
    fn include_dir_private(&mut self, dir: &Path) -> &mut CRTModuleBuildInfo {
        self.private_include_dirs.push(dir.to_path_buf());
        self
    }

    /// Adds an include directory from you one part of your source, to the build's closure so the header
    /// files can be accessed across builds.
    ///
    /// # Arguments
    ///
    /// * `dir` - File system path to the files you want copied to your build output and added to your
    ///           build for inclusion.
    ///
    fn include_dir_and_copy_to_build_tree(&mut self, dir: &Path) -> &mut CRTModuleBuildInfo {
        let out_dir = format!(
            "{}/include",
            env::var_os("OUT_DIR").unwrap().to_str().unwrap()
        );
        let target_include_path = Path::new(out_dir.as_str());
        fs::create_dir_all(target_include_path).expect("Creation of directory failed!");

        let mut terrible_api_hack = vec![];
        terrible_api_hack.push(dir);

        let mut copy_options = CopyOptions::new();
        copy_options.overwrite = true;

        fs_extra::copy_items(
            terrible_api_hack.as_ref(),
            target_include_path,
            &copy_options,
        )
        .expect("Copy failed, check the directory exists");
        self.public_include_dirs
            .push(target_include_path.to_path_buf());

        self
    }

    /// Adds include directory to your module build.
    ///
    /// # Arguments
    ///
    /// * `dir` - File system path to where to find the header files you need.
    /// * `header_type` - Private means the header will be used for this and only this
    ///                   module build. The headers will not be copied to the build directory.
    ///                   Public means the header will be used for this and all downstream
    ///                   dependencies. The files at dir will be copied to the output directory for subsequent
    ///                   module builds and added to its include path.
    /// # Examples
    /// ```should_panic
    /// use aws_crt_c_flags::{CRTModuleBuildInfo, HeaderType};
    /// use std::path::Path;
    /// let mut build_info = CRTModuleBuildInfo::new("aws_crt_common_sys");
    /// build_info.include_dir(Path::new("/opt/include/wherever/you/installed/libcrypto/include"), HeaderType::Private);
    /// build_info.include_dir(Path::new("../source/myproject/include"), HeaderType::Public);
    /// ```
    pub fn include_dir(&mut self, dir: &Path, header_type: HeaderType) -> &mut CRTModuleBuildInfo {
        match header_type {
            HeaderType::Private => {
                return self.include_dir_private(dir);
            }
            HeaderType::Public => {
                return self.include_dir_and_copy_to_build_tree(dir);
            }
        }
    }

    /// Writes generated content to your build directory, for use with things like autoconf output.
    ///
    /// # Arguments
    ///
    /// * `generated_content` - The file contents you want to write.
    /// * `to` - Location relative to your build tree you'd like to write to.
    ///
    ///# Examples
    ///```should_panic
    /// use aws_crt_c_flags::{CRTModuleBuildInfo};
    /// use std::path::Path;
    /// let mut build_info = CRTModuleBuildInfo::new("aws_crt_common_sys");
    /// let content = "test content".to_string();
    /// build_info.write_generated_file_to_output_path(&content, Path::new("include/aws/common/config.h"));
    ///```
    pub fn write_generated_file_to_output_path(
        &mut self,
        generated_content: &str,
        to: &Path,
    ) -> &mut CRTModuleBuildInfo {
        let target_location: String = format!(
            "{}/{}",
            env::var_os("OUT_DIR").unwrap().to_str().unwrap(),
            to.display()
        );
        let target_path = Path::new(target_location.as_str());
        fs::create_dir_all(target_path.parent().unwrap())
            .expect("Creation of output directory failed.");
        fs::write(target_location, generated_content).expect("Writing generated file failed!");

        self
    }

    /// Returns the underlying toolchain that will be used for the build.
    pub fn get_toolchain(&self) -> &Build {
        &self.build_toolchain
    }

    /// Adds the file at path to the build tree
    pub fn file(&mut self, path: &Path) -> &mut CRTModuleBuildInfo {
        self.build_toolchain.file(path);
        self
    }

    /// Attempts to compile, `to_compile` and returns a result on whether or not it succeeded.
    /// This is useful for testing compiler capabilities before including a file or flag in your build.
    ///
    /// # Arguments
    ///
    /// * `to_compile` - C code to attempt compilation of.
    ///
    /// # Examples
    /// ```should_panic
    /// use aws_crt_c_flags::{CRTModuleBuildInfo};
    /// let mut build_info = CRTModuleBuildInfo::new("aws_crt_common_sys");
    /// build_info.try_compile("int main() { return 0; }").expect("This should have compiled");
    /// ```
    pub fn try_compile(&self, to_compile: &str) -> std::result::Result<(), cc::Error> {
        // try_compile prints linker stuff. We don't want that since this is just for testing the
        // compiler capabilities. Suppress it for this scope.
        let _suppress_stdout_cause_the_build_prints_linker_nonsense = Gag::stdout().unwrap();
        let mut test_build = Build::new();
        let output_location = format!(
            "{}/compiler_checks",
            env::var_os("OUT_DIR").unwrap().to_str().unwrap()
        );
        test_build.out_dir(&output_location);
        fs::create_dir_all(&output_location).expect("creation of try compile directory failed");
        let target_location = format!(
            "{}/compiler_checks/check.c",
            env::var_os("OUT_DIR").unwrap().to_str().unwrap()
        );
        fs::write(Path::new(&target_location.as_str()), to_compile).expect("File write failed");
        test_build.file(&target_location);
        let res = test_build.try_compile("test");
        fs::remove_dir_all(&output_location).expect("Cleanup of try compile step failed!");
        res
    }

    /// Returns true if the underlying c compiler uses msvc semantics (e.g. it's not gcc, clang, or intel).
    pub fn follows_msvc_semantics(&self) -> bool {
        self.build_toolchain.get_compiler().is_like_msvc()
    }

    fn load_to_build(&mut self) {
        // add default warning stuff.
        if self.build_toolchain.get_compiler().is_like_msvc() {
            self.private_cflag("/W4")
                .private_cflag("/WX")
                .private_cflag("/MP");
            // relaxes some implicit memory barriers that MSVC normally applies for volatile accesses
            self.private_cflag("/volatile:iso");
            // disable non-constant initializer warning, it's not non-standard, just for Microsoft
            self.private_cflag("/wd4204");
            // disable passing the address of a local warning. Again, not non-standard, just for Microsoft
            self.private_cflag("/wd4221");
        } else {
            self.private_cflag("-Wall")
                .private_cflag("-Werror")
                .private_cflag("-Wstrict-prototypes")
                .private_cflag("-fno-omit-frame-pointer")
                .private_cflag("-Wextra")
                .private_cflag("-pedantic")
                .private_cflag("-Wno-long-long")
                .private_cflag("-fPIC")
                .private_cflag("-Wno-implicit-fallthrough")
                .private_cflag("-Wno-old-style-declaration");
        }

        if self.build_toolchain.is_flag_supported("-Wgnu").is_ok() {
            // -Wgnu-zero-variadic-macro-arguments results in a lot of false positives
            self.private_cflag("-Wgnu");

            /*
            if self
                .build_toolchain
                .is_flag_supported("-Wno-gnu-zero-variadic-macro-arguments")
                .is_ok()
            {
                self.private_cflag("-Wno-gnu-zero-variadic-macro-arguments");
            }*/

            if self
                .try_compile(
                    " #include <netinet/in.h>
            int main() {
            uint32_t x = 0;
            x = htonl(x);
            return (int)x;
            }",
                )
                .is_err()
            {
                self.private_cflag("-Wno-gnu-statement-expression");
            }
        }

        for pub_flag in &self.public_cflags {
            self.build_toolchain.flag_if_supported(pub_flag.as_str());
        }

        for priv_flag in &self.private_cflags {
            self.build_toolchain.flag_if_supported(priv_flag.as_str());
        }

        for pub_define in &self.public_defines {
            self.build_toolchain
                .define(pub_define.0.as_str(), pub_define.1.as_str());
        }

        for priv_define in &self.private_defines {
            self.build_toolchain
                .define(priv_define.0.as_str(), priv_define.1.as_str());
        }

        for include in &self.private_include_dirs {
            self.build_toolchain.include(include);
        }

        for include in &self.public_include_dirs {
            self.build_toolchain.include(include);
        }

        for module in &self.crt_module_deps {
            for pub_flag in &module.public_cflags {
                self.build_toolchain.flag(pub_flag.as_str());
            }

            for pub_define in &self.public_defines {
                self.build_toolchain
                    .define(pub_define.0.as_str(), pub_define.1.as_str());
            }

            for include in &self.public_include_dirs {
                self.build_toolchain.include(include);
            }
        }

        if self.shared_lib {
            self.build_toolchain.shared_flag(true);
        }
    }

    /// Executes the build and if successful stores this object in the environment for the next crate to use.
    pub fn build(&mut self) {
        self.load_to_build();
        self.build_toolchain.compile(self.lib_name.as_str());

        if self.linker_path.is_some() {
            println!(
                "cargo:rustc-link-search={}",
                self.linker_path.as_ref().unwrap().to_str().unwrap()
            );
        }

        for link_flag in &self.link_targets {
            println!("cargo:rustc-link-lib={}", link_flag)
        }

        let mut output_module_file =
            CRTModuleBuildInfo::get_configuration_file(self.crt_module_name.as_str());
        output_module_file
            .write_all(serde_json::to_string(self).unwrap().as_bytes())
            .expect("Writing to the module configuration file failed!");
    }
}
