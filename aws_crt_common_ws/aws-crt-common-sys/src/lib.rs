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

/// This module is a rust translation of the relevant declarations from the aws-c-common
/// header files. They are used from higher-level wrapper modules.
use std::os::raw::{c_char, c_void};

#[repr(C)]
#[non_exhaustive]
pub struct CAllocator {
    pub mem_acquire: extern "C" fn(*mut CAllocator, usize) -> *const c_void,
    pub mem_release: extern "C" fn(*mut CAllocator, *const c_void),
    pub mem_realloc: extern "C" fn(*mut CAllocator, *mut c_void, usize, usize) -> *const c_void,
    pub mem_calloc: extern "C" fn(*mut CAllocator, usize, usize) -> *mut c_void,
    pub impl_ptr: *mut c_void,
}

#[repr(C)]
#[derive(Clone, PartialEq, Debug)]
#[non_exhaustive]
pub enum TraceLevel {
    None = 0,
    Bytes = 1,
    Stacks = 2,
}

#[repr(C)]
#[derive(Clone, PartialEq, Debug)]
#[non_exhaustive]
pub enum CpuFeatureName {
    CLMUL = 0,
    Sse41 = 1,
    See42 = 2,
    Avx2 = 3,
    ArmCrc = 4,
}

#[repr(C)]
#[non_exhaustive]
pub struct CArrayList {
    pub allocator: *const CAllocator,
    pub current_size: usize,
    pub length: usize,
    pub item_size: usize,
    pub data_ptr: *const c_void,
}

#[repr(C)]
#[non_exhaustive]
pub struct CAtomicVar {
    pub val: *const c_void,
}

#[repr(C)]
#[non_exhaustive]
pub struct CString {
    pub allocator: *const CAllocator,
    pub len: usize,
    // there's more stuff here, but it is fine because this never goes on the stack,
    // it's always dynamically allocated. We need length though and this is the simplest way
    // to get it.
}

#[repr(C)]
#[non_exhaustive]
pub struct CByteBuf {
    pub len: usize,
    pub buffer: *const u8,
    pub capacity: usize,
    pub allocator: *const CAllocator,
}

#[repr(C)]
#[non_exhaustive]
pub struct CByteCursor {
    pub len: usize,
    pub ptr: *const u8,
}

impl CByteCursor {
    pub fn new(len: usize, ptr: *const u8) -> Self {
        CByteCursor { len, ptr }
    }
}

#[repr(C)]
pub struct CErrorInfoList {
    pub error_list: *const CErrorInfo,
    pub count: u16,
}

#[repr(C)]
pub struct CErrorInfo {
    pub error_code: i32,
    pub literal_name: *const c_char,
    pub error_str: *const c_char,
    pub lib_name: *const c_char,
    pub formatted_name: *const c_char,
}

#[allow(dead_code)]
extern "C" {
    pub fn aws_common_library_init(allocator: *const CAllocator);
    pub fn aws_common_library_clean_up();
    pub fn aws_mem_tracer_new(
        allocator: *const CAllocator,
        deprecated: *const CAllocator,
        level: TraceLevel,
        stack_frame_size: usize,
    ) -> *mut CAllocator;
    pub fn aws_mem_tracer_destroy(allocator: *const CAllocator) -> *mut CAllocator;
    pub fn aws_mem_tracer_bytes(allocator: *const CAllocator) -> usize;
    pub fn aws_default_allocator() -> *const CAllocator;

    pub fn aws_string_new_from_array(
        allocator: *const CAllocator,
        bytes: *const u8,
        len: usize,
    ) -> *const CString;
    pub fn aws_string_destroy(str: *const CString);
    pub fn aws_string_bytes(str: *const CString) -> *const u8;

    pub fn aws_last_error() -> i32;
    pub fn aws_error_debug_str(err: i32) -> *const c_char;
    pub fn aws_error_str(err: i32) -> *const c_char;

    pub fn aws_array_list_get_at(
        arr_list: *const CArrayList,
        item_ptr: *mut c_void,
        index: usize,
    ) -> i32;
    pub fn aws_array_list_get_at_ptr(
        arr_list: *const CArrayList,
        item_ptr: *const *mut c_void,
        index: usize,
    ) -> i32;

    pub fn aws_array_list_length(arr_list: *const CArrayList) -> usize;

    pub fn aws_register_error_info(error_info: *const CErrorInfoList);
    pub fn aws_unregister_error_info(error_info: *const CErrorInfoList);

    pub fn aws_cpu_has_feature(feature: CpuFeatureName) -> bool;
}
