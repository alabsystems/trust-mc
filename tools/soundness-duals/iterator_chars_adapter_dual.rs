// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! UTF-8 advancement inside real adapter bodies and native iterator bounds.
//! These expectations state Rust behavior; no frozen-oracle run is claimed.

#[kani::proof]
fn unicode_nested_map_equal_safe() {
    assert!("é🦀".chars().map(|c| c as u32).eq([0xe9u32, 0x1f980]));
}

#[kani::proof]
fn unicode_nested_map_byte_decoding_bug() {
    assert!("é".chars().map(|c| c as u32).eq([0xc3u32, 0xa9]));
}

#[kani::proof]
fn unicode_nested_map_wrong_scalar_bug() {
    assert!("é🦀".chars().map(|c| c as u32).eq([0xe9u32, 0x1f40d]));
}

#[kani::proof]
fn chars_ascii_size_hint_safe() {
    assert_eq!("abc".chars().size_hint(), (1, Some(3)));
}

#[kani::proof]
fn chars_unicode_size_hint_safe() {
    assert_eq!("é🦀".chars().size_hint(), (2, Some(6)));
}

#[kani::proof]
fn chars_byte_lower_bound_bug() {
    assert_eq!("é🦀".chars().size_hint(), (6, Some(6)));
}

#[kani::proof]
fn chars_advanced_size_hint_safe() {
    let mut iter = "é🦀".chars();
    assert_eq!(iter.next(), Some('é'));
    assert_eq!(iter.size_hint(), (1, Some(4)));
}

#[kani::proof]
fn mapped_chars_size_hint_safe() {
    assert_eq!("é🦀".chars().map(|c| c as u32).size_hint(), (2, Some(6)));
}

#[kani::proof]
fn take_chars_size_hint_min_safe() {
    assert_eq!("é🦀".chars().take(4).size_hint(), (2, Some(4)));
    assert_eq!("é🦀".chars().take(1).size_hint(), (1, Some(1)));
}

#[kani::proof]
fn take_chars_zero_size_hint_safe() {
    assert_eq!("é🦀".chars().take(0).size_hint(), (0, Some(0)));
}

#[kani::proof]
fn take_array_size_hint_min_safe() {
    assert_eq!([1u8, 2].iter().take(8).size_hint(), (2, Some(2)));
    assert_eq!([1u8, 2].iter().take(1).size_hint(), (1, Some(1)));
}

#[kani::proof]
fn take_zero_keeps_inner_length_bug() {
    assert_eq!([1u8, 2].iter().take(0).size_hint(), (2, Some(2)));
}

struct PanickingHint;

impl Iterator for PanickingHint {
    type Item = u8;

    fn next(&mut self) -> Option<u8> {
        None
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        panic!("Take(0) must not call the inner size_hint")
    }
}

#[kani::proof]
fn take_zero_skips_panicking_inner_hint_safe() {
    assert_eq!(PanickingHint.take(0).size_hint(), (0, Some(0)));
}

#[kani::proof]
fn chars_mutable_reborrow_preserves_owner_safe() {
    let mut iter = "é🦀".chars();
    {
        let borrowed = &mut iter;
        assert_eq!(borrowed.next(), Some('é'));
        assert_eq!(borrowed.size_hint(), (1, Some(4)));
    }
    assert_eq!(iter.next(), Some('🦀'));
    assert_eq!(iter.next(), None);
}

#[kani::proof]
fn chars_nested_map_reborrow_preserves_owner_safe() {
    let mut iter = "é🦀".chars();
    assert!((&mut iter).take(1).map(|c| c as u32).eq([0xe9u32]));
    assert_eq!(iter.next(), Some('🦀'));
}

#[kani::proof]
fn chars_nested_map_reborrow_stale_owner_bug() {
    let mut iter = "é🦀".chars();
    assert!((&mut iter).take(1).map(|c| c as u32).eq([0xe9u32]));
    assert_eq!(iter.next(), Some('é'));
}

#[kani::proof]
fn advanced_map_collect_uses_current_length_safe() {
    let values = [1u8, 2, 3];
    let mut iter = values.iter().map(|x| *x);
    assert_eq!(iter.next(), Some(1));
    let collected: Vec<u8> = iter.collect();
    assert_eq!(collected.len(), 2);
}

#[kani::proof]
fn advanced_map_collect_stale_length_bug() {
    let values = [1u8, 2, 3];
    let mut iter = values.iter().map(|x| *x);
    assert_eq!(iter.next(), Some(1));
    let collected: Vec<u8> = iter.collect();
    assert_eq!(collected.len(), 3);
}
