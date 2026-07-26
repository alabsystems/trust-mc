// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT
// edition: 2021
#![feature(rustc_private)]
//! C string literals are rejected fail-closed with the directory's explicit
//! expected diagnostic; see <https://github.com/rust-lang/rust/issues/113333>.
extern crate libc;
use libc::c_char;

#[kani::proof]
fn check_c_str() {
    assert_eq!(unsafe { *empty_c_str() }, 0);
    let (s, len) = non_empty_c_str();
    assert_ne!(unsafe { *s.offset(0) }, 0);
    assert_eq!(unsafe { *s.offset(len as isize) }, 0);
}

fn empty_c_str() -> *const c_char {
    c"".as_ptr() as *const c_char
}

/// Return a C string and its length (without the null character).
fn non_empty_c_str() -> (*const c_char, usize) {
    (c"hi".as_ptr() as *const c_char, 2)
}
