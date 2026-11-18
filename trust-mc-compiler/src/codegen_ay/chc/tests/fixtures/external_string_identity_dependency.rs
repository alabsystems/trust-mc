// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(dead_code)]
pub use std::string::String as LibraryString;
pub mod alloc {
    pub mod string {
        #[repr(C)]
        pub struct String {
            pub payload: usize,
        }
        impl String {
            #[inline(never)]
            pub fn new() -> Self {
                Self { payload: 7 }
            }
            #[inline(never)]
            pub fn len(&self) -> usize {
                self.payload
            }
            #[inline(never)]
            pub fn is_empty(&self) -> bool {
                false
            }
        }
        impl Default for String {
            fn default() -> Self {
                Self::new()
            }
        }
        impl std::ops::Deref for String {
            type Target = str;
            fn deref(&self) -> &str {
                "foreign"
            }
        }
    }
}
pub trait EvilString {
    fn len(&self) -> usize;
    fn is_empty(&self) -> bool;
}
impl EvilString for LibraryString {
    #[inline(never)]
    fn len(&self) -> usize {
        7
    }
    #[inline(never)]
    fn is_empty(&self) -> bool {
        false
    }
}
pub trait BoundedString: Sized {
    fn bounded_any<const N: usize>() -> Self;
}
impl BoundedString for alloc::string::String {
    fn bounded_any<const N: usize>() -> Self {
        Self { payload: 7 }
    }
}
pub struct Cow<T: ?Sized> {
    pub marker: std::marker::PhantomData<T>,
}
impl std::fmt::Display for Cow<str> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("foreign")
    }
}
