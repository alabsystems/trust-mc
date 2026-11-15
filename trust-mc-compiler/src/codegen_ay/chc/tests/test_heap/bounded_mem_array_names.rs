// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! A type key longer than `MAX_TYPE_KEY_NAME_BYTES` is spelled into the
//! emitted memory-array variable name as a 64-byte prefix plus a 64-bit hash
//! of the full key, while the key itself stays full-length as the heap
//! state's identity for the array (`type_arrays`, pointer-wrapper aliasing,
//! value-sort tables). AY charges every variable occurrence's name against a
//! 1 MiB problem-wide cap; iterator-count.rs minted 8 686-byte closure keys.

use ay_bindings::Sort;

use super::*;
use crate::codegen_ay::chc::heap_state::ChcHeapState;
use crate::codegen_ay::names::{
    MAX_TYPE_KEY_NAME_BYTES, TYPE_KEY_NAME_KEEP_BYTES, bounded_type_key_segment, mem_array_name,
    mem_array_name_pair, store_coerce_name,
};

fn long_closure_key(tail: &str) -> String {
    format!("closure_std__iter__Iterator__try_for_each__call___closure_0__{}{tail}", "u8_".repeat(400))
}

#[test]
fn short_type_keys_are_spelled_verbatim() {
    let at_cap = "a".repeat(MAX_TYPE_KEY_NAME_BYTES);
    for key in ["u8", "std_ptr_Unique_u8", "ref_slice_i32", at_cap.as_str()] {
        assert_eq!(bounded_type_key_segment(key), key);
        assert_eq!(&*mem_array_name("f", key), format!("_f_mem_{key}"));
        let (name, out) = mem_array_name_pair("f", key);
        assert_eq!(&*name, format!("_f_mem_{key}"));
        assert_eq!(out, format!("_f_mem_{key}__out"));
    }
}

#[test]
fn long_type_keys_keep_a_prefix_and_gain_a_hash_of_the_whole_key() {
    let key = long_closure_key("");
    assert!(key.len() > MAX_TYPE_KEY_NAME_BYTES);
    let seg = bounded_type_key_segment(&key);
    assert_eq!(seg.len(), TYPE_KEY_NAME_KEEP_BYTES + 2 + 16);
    assert!(seg.starts_with(&key[..TYPE_KEY_NAME_KEEP_BYTES]));
    assert!(seg[TYPE_KEY_NAME_KEEP_BYTES..].starts_with("_h"));
    assert!(seg.bytes().all(|b| b.is_ascii_alphanumeric() || b == b'_'));
    // Deterministic: every site spelling the key mints the same name.
    assert_eq!(bounded_type_key_segment(&key), seg);
    assert_eq!(&*mem_array_name("main", &key), format!("_main_mem_{seg}"));
    let (name, out) = mem_array_name_pair("main", &key);
    assert_eq!(&*name, format!("_main_mem_{seg}"));
    assert_eq!(out, format!("_main_mem_{seg}__out"));
    assert_eq!(store_coerce_name(&key, 7), format!("__store_coerce_{seg}_7"));
    // Two keys that differ only past the kept prefix stay distinct.
    assert_ne!(bounded_type_key_segment(&long_closure_key("x")), seg);
}

#[test]
fn the_cut_falls_on_a_char_boundary() {
    // A multi-byte char straddling byte 64 must not split.
    let mut key = "a".repeat(TYPE_KEY_NAME_KEEP_BYTES - 1);
    key.push('é');
    key.push_str(&"b".repeat(MAX_TYPE_KEY_NAME_BYTES));
    let seg = bounded_type_key_segment(&key);
    assert!(seg.starts_with(&"a".repeat(TYPE_KEY_NAME_KEEP_BYTES - 1)));
    assert!(seg[TYPE_KEY_NAME_KEEP_BYTES - 1..].starts_with("_h"));
}

/// The heap state keys the array by the FULL type key: the same long key
/// reaches the same array, a sibling key that shares the kept prefix gets its
/// own array, and both emitted names are bounded.
#[test]
fn heap_state_keeps_the_full_key_and_mints_a_bounded_name() {
    let mut heap = ChcHeapState::new();
    let key_a = long_closure_key("");
    let key_b = long_closure_key("x");
    let (name_a, out_a, _, new_a) = heap.get_or_create_type_array(&key_a, Sort::bv8(), "main");
    let (name_a2, _, _, new_a2) = heap.get_or_create_type_array(&key_a, Sort::bv8(), "main");
    let (name_b, _, _, new_b) = heap.get_or_create_type_array(&key_b, Sort::bv8(), "main");
    assert!(new_a && !new_a2 && new_b);
    assert_eq!(name_a, name_a2);
    assert_ne!(name_a, name_b);
    assert!(name_a.len() <= "_main_mem_".len() + TYPE_KEY_NAME_KEEP_BYTES + 18);
    assert!(name_b.len() <= "_main_mem_".len() + TYPE_KEY_NAME_KEEP_BYTES + 18);
    assert_eq!(out_a, format!("{name_a}__out"));
    assert!(heap.type_arrays.contains_key(key_a.as_str()));
    assert!(heap.type_arrays.contains_key(key_b.as_str()));
    assert_eq!(heap.type_arrays.len(), 2);
}
