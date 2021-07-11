/*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 *
 * Licensed under the Apache License, Version 2.0 (the "License").
 * You may not use this file except in compliance with the License.
 * A copy of the License is located at
 *
 *  http://aws.amazon.com/apache2.0
 *
 * or in the "license" file accompanying this file. This file is distributed
 * on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 * express or implied. See the License for the specific language governing
 * permissions and limitations under the License.
 */

use aws_crt_common_sys::{
    aws_common_library_clean_up, aws_common_library_init, aws_default_allocator,
    aws_error_debug_str, aws_error_str, aws_last_error, aws_mem_tracer_bytes,
    aws_mem_tracer_destroy, aws_mem_tracer_new, aws_register_error_info, aws_string_bytes,
    aws_string_destroy, aws_string_new_from_array, aws_unregister_error_info, CAllocator, CString,
    TraceLevel,
};
use std::ffi::CStr;
use std::future::Future;
use std::os::raw::{c_char, c_void};
use std::pin::Pin;
use std::ptr::null_mut;
use std::str::Utf8Error;
use std::sync::{Arc, Mutex, MutexGuard};
use std::task::{Context, Poll, Waker};

/// Trait for deep copying (cloning) an object. The operation can fail so it returns
/// a result with an error code upon failure.
pub trait TryClone<T> {
    fn try_clone(&self) -> Result<T, i32>;
}

/// Trait that gives a c-style non-const pointer to an underlying resource.
/// Ideally you use this when calling an ffi function that needs a pointer
/// to your wrapped Rust object.
pub trait MutableNativeResource<T> {
    fn get_native_resource_mut(&mut self) -> *mut T;
}

/// Trait that gives a c-style const pointer to an underlying resource.
/// Ideally you use this when calling an ffi function that needs a pointer
/// to your wrapped Rust object.
pub trait NativeResource<T> {
    fn get_native_resource(&self) -> *const T;
}

pub struct FutureSharedState<T> {
    data: Option<T>,
    waker: Option<Waker>,
}

/// Simple future implementation for driving async futures
/// from C-style callbacks. For this scenario, a pointer to FutureSharedState is used as your user_data pointer.
///
/// Upon creation call, CallbackFuture::to_callback_ptr() to get the pointer to pass to C functions.
/// When your callback completes, fill-in an instance of type T, and call FutureSharedState::resolve()
/// with the user_data pointer from your c callback.
///
/// Assuming you do these things, you've just converted C-style async code into co-routine ready
/// Rust futures.
///
#[derive(Clone)]
pub struct CallbackFuture<T> {
    data: Arc<Mutex<FutureSharedState<T>>>,
}

impl<T> FutureSharedState<T> {
    ///
    /// Completes the future for callback_data with result as the future's output.
    ///
    pub fn resolve(callback_data: *const c_void, result: T) {
        // sound assuming a valid instance of this class.
        unsafe {
            let shared_state_ptr = Arc::from_raw(callback_data as *mut Mutex<FutureSharedState<T>>);

            let mut res_option = shared_state_ptr.lock().unwrap();
            res_option.data = Some(result);

            if let Some(waker) = res_option.waker.take() {
                waker.wake();
            }
        }
    }
}

impl<T> Future for CallbackFuture<T> {
    type Output = T;

    fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
        let mut option_val: MutexGuard<FutureSharedState<T>> = self.data.lock().unwrap();
        if option_val.data.is_none() {
            option_val.waker = Some(cx.waker().clone());
            return Poll::Pending;
        }

        return Poll::Ready(option_val.data.take().expect("We're in a ready state implying the future has completed but the underlying value hasn't been set!"));
    }
}

impl<T> CallbackFuture<T> {
    /// Returns an instance of CallbackFuture to wrap a c-style async function, where T
    /// is the result of future.await. When ready to complete the future, invoke:
    ///
    /// FutureSharedState::resolve() with an instance of T and the void * pointer
    /// to the c-function's user_data.
    ///
    /// You'll want to pass the result of to_callback_ptr as your initial user_data pointer to
    /// the c function.
    pub fn new() -> CallbackFuture<T> {
        CallbackFuture {
            data: Arc::new(Mutex::new(FutureSharedState {
                data: None,
                waker: None,
            })),
        }
    }

    ///
    /// Returns a c-style void * pointer to the future's shared state.
    ///
    pub fn to_callback_ptr(&self) -> *const c_void {
        Arc::into_raw(self.data.clone()) as *const c_void
    }
}

/// Turns a Rust literal into a 'static CStr
///
/// The produced `*const c_char` has a lifetime suitable to be passed to
/// functions like `aws_register_error_info` that require that it's arguments
/// live for the duration of the program.
///
/// The literal may be produced by nested macros, but must eventually be a literal.
/// This is enforced by `concat!`
#[macro_export]
macro_rules! static_c_str {
    ($inp: expr) => {
        concat!($inp, "\0").as_ptr() as *const ::std::os::raw::c_char
    };
}

pub fn init(allocator: &dyn NativeResource<CAllocator>) {
    // initializes the aws-c-common library. Loads error strings and sets up any static/global
    // state. It's fine to just let this leak. Later we may add an API handle wrapper and then
    // come back with clean up functions in an RAII wrapper.
    unsafe {
        aws_common_library_init(allocator.get_native_resource());
    }
    register_errors();
}

pub fn clean_up() {
    unregister_errors();
    unsafe {
        aws_common_library_clean_up();
    }
}

/// Returns the last error that occurred on the calling thread.
pub fn last_error() -> i32 {
    return unsafe { aws_last_error() };
}

/// Returns the error represented by error_code as a detailed debug string.
pub fn error_debug_str(error_code: i32) -> Result<&'static str, Utf8Error> {
    // this function always returns a static c-string. Even if the error code was invalid
    // it will point to static memory.
    let error_str = unsafe { aws_error_debug_str(error_code) };
    // convert the underlying c string memory into a rust representation of it.
    // error_str cannot be null.
    let error_c_str = unsafe { CStr::from_ptr(error_str) };
    error_c_str.to_str()
}

/// Returns the error represented by error_code as a string.
pub fn error_str(error_code: i32) -> Result<&'static str, Utf8Error> {
    // this function always returns a static c-string. Even if the error code was invalid
    // it will point to static memory.
    let error_str = unsafe { aws_error_str(error_code) };
    // convert the underlying c string memory into a rust representation of it.
    // error_str cannot be null.
    let error_c_str = unsafe { CStr::from_ptr(error_str) };
    error_c_str.to_str()
}

/// Create a CErrorInfo Struct
///
/// The produced struct and members have a `'static` lifetime, safe to use
/// for the duration of the program. See `DEFINE_ERROR_INFO_COMMON` for
/// the parallel c-preprocessor macro.
#[macro_export]
macro_rules! error_info {
    ($error_code:ident, $error_str: literal) => {
        CErrorInfo {
            error_code: ($error_code),
            literal_name: static_c_str!(stringify!($error_code)),
            error_str: static_c_str!($error_str),
            lib_name: static_c_str!("aws-crt-rs"),
            formatted_name: static_c_str!(concat!(
                "aws-crt-rs: ",
                stringify!($error_code),
                ", ",
                $error_str
            )),
        }
    };
}

/// Default allocator to use for most of this crate's APIs. This is usually the one
/// you want, unless you're testing or profiling.
#[non_exhaustive]
pub struct DefaultAllocator {
    c_allocator: *const CAllocator,
}

impl DefaultAllocator {
    pub fn new() -> DefaultAllocator {
        // aws_default_allocator() always returns a valid address to static memory.
        // it does not need a destructor since the allocator is static memory.
        unsafe {
            let alloc = DefaultAllocator {
                c_allocator: aws_default_allocator(),
            };
            return alloc;
        }
    }
}

impl NativeResource<CAllocator> for DefaultAllocator {
    fn get_native_resource(&self) -> *const CAllocator {
        self.c_allocator
    }
}

/// This is a good debugging allocator that will provide diagnositics on memory errors and leaks.
///
/// This is most useful for tests.
#[non_exhaustive]
pub struct TracingAllocator {
    c_allocator: *const CAllocator,
}

impl TracingAllocator {
    pub fn new(level: TraceLevel, frames_per_stack: usize) -> TracingAllocator {
        // aws_default_allocator() always returns a valid address and it's static memory so it
        // doesn't need to be cleaned up. However, aws_mem_tracer_new() allocates under the hood,
        // and this memory will be reclaimed in the destructor. If the destructor doesn't run,
        // the worst that will happen is a memory leak.
        unsafe {
            let default_allocator = aws_default_allocator();
            let alloc = TracingAllocator {
                c_allocator: aws_mem_tracer_new(
                    default_allocator,
                    null_mut(),
                    level,
                    frames_per_stack,
                ),
            };
            return alloc;
        }
    }

    /// returns the count of currently allocated bytes.
    pub fn allocated_bytes(&self) -> usize {
        // If we have an instance of this class, c_allocator is assumed valid.
        // simply returns the count of currently allocated bytes.
        unsafe {
            return aws_mem_tracer_bytes(self.c_allocator);
        }
    }
}

impl NativeResource<CAllocator> for TracingAllocator {
    fn get_native_resource(&self) -> *const CAllocator {
        self.c_allocator
    }
}

impl Drop for TracingAllocator {
    fn drop(&mut self) {
        // aws_mem_tracer_destroy() returns the wrapped allocator, but since in new()
        // it's specified as the default_allocator, it doesn't need to be cleaned up.
        unsafe {
            let _ = aws_mem_tracer_destroy(self.c_allocator);
        }
    }
}

/// String type which wraps the internal aws_string structure. This type is immutable.
#[non_exhaustive]
pub struct AwsString {
    c_str: *const CString,
    owned: bool,
}

impl AwsString {
    /// Creates a new String for a Rust std::string::String instance.
    ///
    /// Returns a result containing the new String or an int-based error code on failure.
    pub fn new_from_std_string(
        allocator: &dyn NativeResource<CAllocator>,
        str: &String,
    ) -> Result<AwsString, i32> {
        return AwsString::new_from_array(allocator, str.as_bytes());
    }

    /// Creates a new String for a Rust str.
    ///
    /// Returns a result containing the new String or an int-based error code on failure.
    pub fn new_from_str(
        allocator: &dyn NativeResource<CAllocator>,
        str: &str,
    ) -> Result<AwsString, i32> {
        let bytes = str.as_bytes();
        return AwsString::new_from_array(allocator, bytes);
    }

    pub fn new_from_cstr(c_str: *const CString) -> AwsString {
        AwsString {
            c_str,
            owned: false,
        }
    }

    /// Creates a new string from an arbitrary array of utf-8 bytes.
    ///
    /// Returns a result containing the new String or an int-based error code on failure.
    pub fn new_from_array(
        allocator: &dyn NativeResource<CAllocator>,
        str_data: &[u8],
    ) -> Result<AwsString, i32> {
        // assumes allocator is valid and str_data is not null.
        // since the underlying allocation can fail, returns an error
        // if aws_string_new_from_array() fails.
        // The memory from this function is cleaned up in the destructor. If
        // the destructor isn't run, the worse that will happen is a memory leak.
        unsafe {
            let c_str_ptr = aws_string_new_from_array(
                allocator.get_native_resource(),
                str_data.as_ptr(),
                str_data.len(),
            );
            if c_str_ptr.is_null() {
                return Err(last_error());
            }

            return Ok(AwsString {
                c_str: c_str_ptr,
                owned: true,
            });
        }
    }

    /// Returns the length of the string in bytes, not including any null terminators.
    pub fn length(&self) -> usize {
        // This is sound if you have an instance of this class.
        unsafe {
            return (*self.c_str).len;
        }
    }

    /// Returns a pointer to an array of utf8 characters for the underlying String
    pub fn as_ptr(&self) -> *const u8 {
        // This is sound if you have an instance of this class.
        unsafe {
            return aws_string_bytes(self.c_str);
        }
    }

    /// Returns a pointer to an array of utf8 characters as a c-string, including the null terminator.
    /// **WARNING**
    ///
    /// It is the callers responsibility to ensure that the underlying memory is not freed too early.
    ///
    /// ```no_run
    /// # #![allow(unused_must_use)]
    /// // THIS IS UB & a use-after-free vulnerability!
    /// use aws_crt_common::AwsString;
    /// let allocator = todo!();
    /// let ptr = AwsString::new_from_str(allocator, "Hello")
    ///                       .expect("Creation of c string failed!")
    ///                       .as_c_str();
    /// unsafe {
    ///     *ptr;
    /// }
    /// ```
    ///
    /// Instead, you must ensure that the AwsString lives long enough:
    /// ```no_run
    /// # #![allow(unused_must_use)]
    /// use aws_crt_common::AwsString;
    /// let allocator = todo!();
    /// let aws_str = AwsString::new_from_str(allocator, "Hello")
    ///                       .expect("Creation of c string failed!");
    /// let ptr = aws_str.as_c_str();
    /// unsafe {
    ///     *ptr;
    /// }
    /// ```
    pub fn as_c_str(&self) -> *const c_char {
        // This is sound if you have an instance of this class.
        unsafe {
            return aws_string_bytes(self.c_str) as *const c_char;
        }
    }
}

impl ToString for AwsString {
    fn to_string(&self) -> String {
        // this is sound if you have an instance of this class and the original AwsString is valid utf-8
        unsafe {
            let slice = std::slice::from_raw_parts(self.as_ptr(), self.length());
            return String::from_utf8_unchecked(Vec::from(slice));
        }
    }
}

impl Into<String> for AwsString {
    fn into(self) -> String {
        self.to_string()
    }
}

impl Drop for AwsString {
    fn drop(&mut self) {
        if self.owned {
            // sound assuming you have an instance of this class.
            unsafe {
                aws_string_destroy(self.c_str);
            }
        }
    }
}

impl NativeResource<CString> for AwsString {
    fn get_native_resource(&self) -> *const CString {
        self.c_str
    }
}

#[allow(dead_code)]
pub(crate) fn register_errors() {
    unsafe { aws_register_error_info(&error_codes::CRUST_ERRORS) }
}

#[allow(dead_code)]
pub(crate) fn unregister_errors() {
    unsafe { aws_unregister_error_info(&error_codes::CRUST_ERRORS) }
}

pub mod error_codes {
    use aws_crt_common_sys::{CErrorInfo, CErrorInfoList};

    pub const INVALID_UTF8: i32 = 0x3400;
    const RUST_ERRORS: [CErrorInfo; 1] = [error_info!(INVALID_UTF8, "String was not valid UTF-8")];

    pub const CRUST_ERRORS: CErrorInfoList = CErrorInfoList {
        error_list: RUST_ERRORS.as_ptr(),
        count: RUST_ERRORS.len() as u16,
    };
}
