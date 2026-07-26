// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! SMT sort name generation for Rust types.
//!
//! Canonical sort name strings for Vec, Option, Slice, Dyn, Closure,
//! and iterator instantiations. Used across `codegen_types*`, `sort_inference*`,
//! collection stubs, and `memory_type_key_tables`.
//!
//! Part of #2304, #2408.

use std::borrow::Cow;
use std::fmt::Write as _;

/// Vec sort name: `Vec_{type_suffix}`.
pub fn vec_sort_name(type_suffix: &str) -> String {
    let mut s = String::with_capacity(type_suffix.len() + 4);
    s.push_str("Vec_");
    s.push_str(type_suffix);
    s
}

/// Option sort name: `Option_{type_suffix}`.
pub fn option_sort_name(type_suffix: &str) -> String {
    let mut s = String::with_capacity(type_suffix.len() + 7);
    s.push_str("Option_");
    s.push_str(type_suffix);
    s
}

/// Slice sort name: `Slice_{type_suffix}`.
pub fn slice_sort_name(type_suffix: &str) -> String {
    let mut s = String::with_capacity(type_suffix.len() + 6);
    s.push_str("Slice_");
    s.push_str(type_suffix);
    s
}

/// Dyn trait sort name: `Dyn_{trait_name}`.
pub fn dyn_sort_name(trait_name: &str) -> String {
    let mut s = String::with_capacity(trait_name.len() + 4);
    s.push_str("Dyn_");
    s.push_str(trait_name);
    s
}

/// Closure sort name: `Closure_{id}`.
///
/// Canonical SMT sort name for closure types, used in both type translation
/// (`codegen_types.rs`) and aggregate construction (`codegen_stmt_aggregate.rs`).
pub fn closure_sort_name(closure_id: usize) -> String {
    let mut s = String::with_capacity(16);
    s.push_str("Closure_");
    let _ = write!(&mut s, "{closure_id}");
    s
}

/// Coroutine sort name: `Coroutine_{id}`.
///
/// Part of #1351: Canonical SMT sort name for coroutine types. Mirrors
/// `closure_sort_name` but adds a `fld_state` discriminant field for
/// the coroutine state machine.
pub fn coroutine_sort_name(coroutine_id: usize) -> String {
    let mut s = String::with_capacity(16);
    s.push_str("Coroutine_");
    let _ = write!(&mut s, "{coroutine_id}");
    s
}

/// Closure capture field name: `cap_{index}`.
///
/// Names the N-th captured upvar in a closure datatype. Returns `Cow::Borrowed`
/// for indices 0-15 (the common case), falling back to a formatted owned string.
pub fn capture_field_name(index: usize) -> Cow<'static, str> {
    static NAMES: [&str; 16] = [
        "cap_0", "cap_1", "cap_2", "cap_3", "cap_4", "cap_5", "cap_6", "cap_7", "cap_8", "cap_9",
        "cap_10", "cap_11", "cap_12", "cap_13", "cap_14", "cap_15",
    ];
    if index < NAMES.len() {
        Cow::Borrowed(NAMES[index])
    } else {
        let mut name = String::with_capacity(16);
        name.push_str("cap_");
        let _ = write!(&mut name, "{index}");
        Cow::Owned(name)
    }
}

/// PolymorphicIter sort name: `PolymorphicIter_{type_suffix}`.
pub fn polymorphic_iter_sort_name(type_suffix: &str) -> String {
    let mut s = String::with_capacity(type_suffix.len() + 17);
    s.push_str("PolymorphicIter_");
    s.push_str(type_suffix);
    s
}

/// Array IntoIter sort name: `IntoIter_{type_suffix}`.
pub fn into_iter_sort_name(type_suffix: &str) -> String {
    let mut s = String::with_capacity(type_suffix.len() + 9);
    s.push_str("IntoIter_");
    s.push_str(type_suffix);
    s
}

/// Vec IntoIter sort name: `VecIntoIter_{type_suffix}`.
pub fn vec_into_iter_sort_name(type_suffix: &str) -> String {
    let mut s = String::with_capacity(type_suffix.len() + 12);
    s.push_str("VecIntoIter_");
    s.push_str(type_suffix);
    s
}

/// HashSet IntoIter sort name: `HashSetIntoIter_{type_suffix}`.
pub fn hashset_into_iter_sort_name(type_suffix: &str) -> String {
    let mut s = String::with_capacity(type_suffix.len() + 16);
    s.push_str("HashSetIntoIter_");
    s.push_str(type_suffix);
    s
}

/// HashMap IntoIter sort name: `HashMapIntoIter_{key_suffix}_{val_suffix}`.
pub fn hashmap_into_iter_sort_name(key_suffix: &str, val_suffix: &str) -> String {
    let mut s = String::with_capacity(key_suffix.len() + val_suffix.len() + 17);
    s.push_str("HashMapIntoIter_");
    s.push_str(key_suffix);
    s.push('_');
    s.push_str(val_suffix);
    s
}

// Tests live in trust_mc-compiler (standalone test binaries cannot link rustc sysroot dylibs).
