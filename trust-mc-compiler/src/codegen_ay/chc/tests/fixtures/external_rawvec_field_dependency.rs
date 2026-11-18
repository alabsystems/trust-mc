// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(dead_code)]

#[repr(C)]
pub struct RawVec {
    pub ptr: *mut u64,
    pub cap: usize,
}
impl RawVec {
    #[inline(never)]
    pub fn ptr(&self) -> *mut u64 {
        self.ptr
    }
}
#[repr(C)]
pub struct Vec {
    pub buf: RawVec,
    pub len: usize,
}
pub trait ForeignPtr {
    fn ptr(&self) -> *mut u64;
}
impl ForeignPtr for std::vec::Vec<u64> {
    fn ptr(&self) -> *mut u64 {
        std::ptr::null_mut()
    }
}
