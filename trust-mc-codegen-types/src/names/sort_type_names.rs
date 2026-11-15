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

// ---------------------------------------------------------------------------
// Recognizers. Every test of a sort's NAME lives in `names`, beside the code
// that builds the name (design trust-mc-reds-final §7.2, T3-1), so a change of
// naming scheme changes its readers in the same module. The engine lint
// `test_sort_name_single_rule` refuses a string predicate on a sort name
// anywhere else under `codegen_ay`.
// ---------------------------------------------------------------------------

/// A [`vec_sort_name`] sort.
pub fn is_vec_sort_name(name: &str) -> bool {
    name.starts_with("Vec_")
}

/// A sort of the Vec model family: [`vec_sort_name`], `VecIter_*`,
/// [`vec_into_iter_sort_name`].
pub fn is_vec_family_sort_name(name: &str) -> bool {
    name.starts_with("Vec")
}

/// An Option sort: a model [`option_sort_name`] sort (or the bare fixture
/// name `Option`), or the sort of the `Option` ADT itself ([`super::adt_sort_is`]).
pub fn is_option_sort_name(name: &str) -> bool {
    name == "Option"
        || name.starts_with("Option_")
        || super::adt_sort_is(name, super::known_adt::OPTION)
}

/// A [`slice_sort_name`] sort.
pub fn is_slice_sort_name(name: &str) -> bool {
    name.starts_with("Slice_")
}

/// A sort whose name mentions the slice model anywhere (`Slice_*`,
/// `SliceIter_*`, `VecIter_Slice_*`): a value carrying a slice's `fld_ptr`.
pub fn sort_name_mentions_slice(name: &str) -> bool {
    name.contains("Slice")
}

/// A [`dyn_sort_name`] sort.
pub fn is_dyn_sort_name(name: &str) -> bool {
    name.starts_with("Dyn_")
}

/// A [`closure_sort_name`] sort.
pub fn is_closure_sort_name(name: &str) -> bool {
    name.starts_with("Closure_")
}

/// A [`vec_into_iter_sort_name`] sort.
pub fn is_vec_into_iter_sort_name(name: &str) -> bool {
    name.starts_with("VecIntoIter")
}

/// A [`hashmap_into_iter_sort_name`] sort.
pub fn is_hashmap_into_iter_sort_name(name: &str) -> bool {
    name.starts_with("HashMapIntoIter")
}

/// A [`hashset_into_iter_sort_name`] sort.
pub fn is_hashset_into_iter_sort_name(name: &str) -> bool {
    name.starts_with("HashSetIntoIter")
}

/// A `SliceIter_*` model sort.
pub fn is_slice_iter_sort_name(name: &str) -> bool {
    name.starts_with("SliceIter_")
}

/// Which collection an `IntoIter` model sort iterates, read from the name its
/// builder gave it: a HashMap or HashSet model, an array's ([`into_iter_sort_name`]
/// over a [`polymorphic_iter_sort_name`], or the bare `IntoIter`), else a Vec's.
pub fn into_iter_sort_source(name: &str) -> IntoIterSource {
    if name.contains("HashMap") {
        IntoIterSource::HashMap
    } else if name.contains("HashSet") {
        IntoIterSource::HashSet
    } else if name == "IntoIter" || name.contains("PolymorphicIter") {
        IntoIterSource::Array
    } else {
        IntoIterSource::Vec
    }
}

/// See [`into_iter_sort_source`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum IntoIterSource {
    HashMap,
    HashSet,
    Array,
    Vec,
}

/// A synthetic iterator model sort with no MIR type to classify it by
/// (`*IntoIter*`, `*Iter_*`, `*Iter`).
pub fn is_iterator_model_sort_name(name: &str) -> bool {
    name.contains("IntoIter") || name.contains("Iter_") || name.ends_with("Iter")
}

/// The BMC lane's `RawVec` model sort.
pub const RAWVEC_MODEL_SORT: &str = "RawVec";

/// The BMC lane's `Layout` model sort.
pub const LAYOUT_MODEL_SORT: &str = "Layout";

/// A sort whose name mentions `RawVec` (the model sort, or an ADT over it).
pub fn sort_name_mentions_rawvec(name: &str) -> bool {
    name.contains("RawVec")
}

/// A `Copied<I>` or `Cloned<I>` sort: the ADT's own sort, or the bare fixture
/// names.
pub fn is_copied_or_cloned_sort_name(name: &str) -> bool {
    name == "Copied"
        || name == "Cloned"
        || super::adt_sort_is(name, super::known_adt::COPIED)
        || super::adt_sort_is(name, super::known_adt::CLONED)
}

/// A `TypeId` sort: the ADT's own sort, or the bare name a stub gives it.
pub fn is_type_id_sort_name(name: &str) -> bool {
    name == "TypeId" || super::adt_sort_is(name, super::known_adt::TYPE_ID)
}

/// A `str::Chars` sort, or a model sort over one.
pub fn sort_name_mentions_chars(name: &str) -> bool {
    name.contains("Chars")
}

/// An allocation `Result<_, AllocError>` sort (#2618).
pub fn is_alloc_result_sort_name(name: &str) -> bool {
    name.contains("Result") && name.contains("AllocError")
}

/// A BigInt / BigUint / Ratio model sort (value semantics).
pub fn is_bignum_sort_name(name: &str) -> bool {
    name.contains("BigInt") || name.contains("BigUint") || name.contains("Ratio")
}

// Tests live in trust_mc-compiler (standalone test binaries cannot link rustc sysroot dylibs).
