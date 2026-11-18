// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(dead_code)]
extern crate external_vec_lookalike;
use external_vec_lookalike::{ForeignPtr, RawVec};

pub fn external_rawvec_ptr(value: &RawVec) -> *mut u64 {
    value.ptr()
}
pub fn external_trait_ptr(value: &std::vec::Vec<u64>) -> *mut u64 {
    ForeignPtr::ptr(value)
}
pub fn indirect_ptr(function: fn(&RawVec) -> *mut u64, value: &RawVec) -> *mut u64 {
    function(value)
}
pub fn external_rawvec_field(value: &external_vec_lookalike::Vec) -> &RawVec {
    &value.buf
}
