// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT

#[macro_export]
#[allow(clippy::crate_in_macro_def)]
macro_rules! generate_string_iter {
    () => {
        struct KaniBytesIter {
            ptr: *const u8,
            len: usize,
        }

        impl KaniBytesIter {
            fn new(ptr: *const u8, len: usize) -> Self {
                KaniBytesIter { ptr, len }
            }

            fn from_str(source: &str) -> Self {
                KaniBytesIter::new(source.as_ptr(), source.len())
            }
        }

        impl KaniIter for KaniBytesIter {
            type Item = u8;

            fn nth(&self, i: usize) -> Self::Item {
                // SAFETY: callers use this immutable iterator only for indices
                // proven to be within bounds of the original string-backed byte
                // slice.
                unsafe { *self.ptr.wrapping_add(i) }
            }

            fn first(&self) -> Self::Item {
                // SAFETY: same contract as `nth(0)`.
                unsafe { *self.ptr }
            }

            fn assumption(&self) -> bool {
                // SAFETY: mirrors the existing pointer-backed iterator
                // contract for an immutable byte slice.
                unsafe { mem::is_allocated(self.ptr as *const (), self.len) }
            }

            fn len(&self) -> usize {
                self.len
            }
        }

        struct KaniAsciiCharsIter {
            bytes: KaniBytesIter,
        }

        impl KaniAsciiCharsIter {
            fn new(ptr: *const u8, len: usize) -> Self {
                KaniAsciiCharsIter { bytes: KaniBytesIter::new(ptr, len) }
            }

            fn from_str(source: &str) -> Self {
                KaniAsciiCharsIter::new(source.as_ptr(), source.len())
            }
        }

        impl KaniIter for KaniAsciiCharsIter {
            type Item = char;

            fn nth(&self, i: usize) -> Self::Item {
                self.bytes.nth(i) as char
            }

            fn first(&self) -> Self::Item {
                self.bytes.first() as char
            }

            fn assumption(&self) -> bool {
                self.bytes.assumption()
            }

            fn len(&self) -> usize {
                self.bytes.len()
            }
        }

        fn utf8_char_width(first: u8) -> usize {
            if first < 0x80 {
                1
            } else if first & 0b1110_0000 == 0b1100_0000 {
                2
            } else if first & 0b1111_0000 == 0b1110_0000 {
                3
            } else {
                4
            }
        }

        fn decode_utf8_char(bytes: &KaniBytesIter, start: usize) -> Option<(char, usize)> {
            if start >= bytes.len() {
                return None;
            }

            let first = bytes.nth(start);
            let width = utf8_char_width(first);
            if start + width > bytes.len() {
                return None;
            }

            let scalar = match width {
                1 => first as u32,
                2 => (((first & 0x1f) as u32) << 6) | ((bytes.nth(start + 1) & 0x3f) as u32),
                3 => {
                    (((first & 0x0f) as u32) << 12)
                        | (((bytes.nth(start + 1) & 0x3f) as u32) << 6)
                        | ((bytes.nth(start + 2) & 0x3f) as u32)
                }
                4 => {
                    (((first & 0x07) as u32) << 18)
                        | (((bytes.nth(start + 1) & 0x3f) as u32) << 12)
                        | (((bytes.nth(start + 2) & 0x3f) as u32) << 6)
                        | ((bytes.nth(start + 3) & 0x3f) as u32)
                }
                _ => unreachable!(),
            };

            core_path::char::from_u32(scalar).map(|ch| (ch, width))
        }

        fn bytes_are_ascii(bytes: &KaniBytesIter) -> bool {
            let mut index = 0usize;
            while index < bytes.len() {
                if bytes.nth(index) & 0x80 != 0 {
                    return false;
                }
                index += 1;
            }
            true
        }
    };
}

#[macro_export]
#[allow(clippy::crate_in_macro_def)]
macro_rules! generate_string_iter_root_helpers {
    () => {
        #[doc(hidden)]
        #[kanitool::fn_marker = "StrBytesNthHelper"]
        pub fn kani_str_bytes_nth(source: &str, index: usize) -> Option<u8> {
            let iter = KaniBytesIter::from_str(source);
            if index < iter.len() { Some(iter.nth(index)) } else { None }
        }

        #[doc(hidden)]
        #[kanitool::fn_marker = "StrCharsNthHelper"]
        pub fn kani_str_chars_nth(source: &str, index: usize) -> Option<char> {
            let bytes = KaniBytesIter::from_str(source);
            if bytes_are_ascii(&bytes) {
                let iter = KaniAsciiCharsIter::from_str(source);
                return if index < iter.len() { Some(iter.nth(index)) } else { None };
            }

            let mut char_index = 0usize;
            let mut byte_index = 0usize;

            while byte_index < bytes.len() {
                let (ch, width) = decode_utf8_char(&bytes, byte_index)?;
                if char_index == index {
                    return Some(ch);
                }
                char_index += 1;
                byte_index += width;
            }

            None
        }
    };
}

#[macro_export]
#[allow(clippy::crate_in_macro_def)]
macro_rules! generate_string_iter_internal {
    () => {
        use super::KaniIter;

        #[doc(hidden)]
        #[kanitool::fn_marker = "StrBytesNthHelper"]
        pub fn kani_str_bytes_nth(source: &str, index: usize) -> Option<u8> {
            let iter = super::KaniBytesIter::from_str(source);
            if index < iter.len() { Some(iter.nth(index)) } else { None }
        }

        #[doc(hidden)]
        #[kanitool::fn_marker = "StrCharsNthHelper"]
        pub fn kani_str_chars_nth(source: &str, index: usize) -> Option<char> {
            let bytes = super::KaniBytesIter::from_str(source);
            if super::bytes_are_ascii(&bytes) {
                let iter = super::KaniAsciiCharsIter::from_str(source);
                return if index < iter.len() { Some(iter.nth(index)) } else { None };
            }

            let mut char_index = 0usize;
            let mut byte_index = 0usize;

            while byte_index < bytes.len() {
                let (ch, width) = super::decode_utf8_char(&bytes, byte_index)?;
                if char_index == index {
                    return Some(ch);
                }
                char_index += 1;
                byte_index += width;
            }

            None
        }
    };
}
