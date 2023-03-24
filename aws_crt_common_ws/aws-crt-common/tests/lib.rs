#[cfg(test)]
mod tests {
    use aws_crt_common::{
        clean_up, error_codes, error_debug_str, error_info, error_str, init, static_c_str,
        AwsString, NativeResource, TracingAllocator,
    };
    use aws_crt_common_sys::{CErrorInfo, TraceLevel};
    use serial_test::serial;
    use std::ffi::CStr;
    use std::ptr::null;

    #[test]
    #[serial]
    fn test_allocator_safety() {
        let allocator = TracingAllocator::new(TraceLevel::Stacks, 16);
        init(&allocator);
        assert_ne!(null(), allocator.get_native_resource());
        clean_up();
    }

    #[test]
    #[serial]
    fn test_string() {
        let bytes = "Hello World";
        let allocator = TracingAllocator::new(TraceLevel::Stacks, 16);
        init(&allocator);

        {
            let str = AwsString::new_from_array(&allocator, bytes.as_bytes())
                .expect("String init failed!");
            assert_eq!(bytes.len(), str.length());

            let rs_str_conv = AwsString::to_string(&str);
            assert_eq!(bytes, rs_str_conv);
        }

        clean_up();
        assert_eq!(0, allocator.allocated_bytes());
    }

    #[test]
    #[serial]
    fn test_error_str() {
        let allocator = TracingAllocator::new(TraceLevel::Stacks, 16);
        init(&allocator);
        assert_eq!("Success.", error_str(0).expect("String conversion failed!"));
        clean_up();
    }

    #[test]
    #[serial]
    fn test_error_debug_str() {
        let allocator = TracingAllocator::new(TraceLevel::Stacks, 16);
        init(&allocator);
        assert_eq!(
            "aws-c-common: AWS_ERROR_SUCCESS, Success.",
            error_debug_str(0).expect("String conversion failed!")
        );
        clean_up();
    }

    #[test]
    fn test_static_cstr() {
        let static_c_str = static_c_str!("INVALID_UTF8");
        unsafe { assert_eq!(CStr::from_ptr(static_c_str).to_str(), Ok("INVALID_UTF8")) }
    }

    #[test]
    fn test_error_info() {
        const INVALID_UTF8: i32 = 0x3400;
        let error_info: CErrorInfo = error_info!(INVALID_UTF8, "String was not valid UTF-8");
        assert_eq!(error_info.error_code, 0x3400);
        unsafe {
            assert_eq!(
                CStr::from_ptr(error_info.literal_name).to_str(),
                Ok("INVALID_UTF8")
            );
            assert_eq!(
                CStr::from_ptr(error_info.error_str).to_str(),
                Ok("String was not valid UTF-8")
            );
            assert_eq!(
                CStr::from_ptr(error_info.lib_name).to_str(),
                Ok("aws-crt-rs")
            );
            assert_eq!(
                CStr::from_ptr(error_info.formatted_name).to_str(),
                Ok("aws-crt-rs: INVALID_UTF8, String was not valid UTF-8")
            );
        }
    }

    #[test]
    #[serial]
    fn test_error_str_custom() {
        let allocator = TracingAllocator::new(TraceLevel::Stacks, 16);
        init(&allocator);
        assert_eq!(
            error_debug_str(error_codes::INVALID_UTF8).expect("String conversion failed"),
            "aws-crt-rs: INVALID_UTF8, String was not valid UTF-8"
        );

        assert_eq!(
            error_str(error_codes::INVALID_UTF8).expect("String conversion failed"),
            "String was not valid UTF-8"
        );

        assert_eq!(allocator.allocated_bytes(), 0);
        clean_up();

        assert_eq!(
            error_str(error_codes::INVALID_UTF8).expect("String conversion failed"),
            "Unknown Error Code"
        );
    }
}
