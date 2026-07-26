// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Sort short name: concise human-readable names for AY sorts.
//!
//! Extracted from names.rs — Part of #2408.

use std::borrow::Cow;
use std::fmt::Write as _;

/// Get a short, readable name for a AY sort.
///
/// Produces concise names for use in tuple and Option datatype naming:
/// - `bool`, `int`, `real` for theory sorts
/// - `bv{width}` for bitvectors (e.g., `bv32`, `bv64`)
/// - `arr_{idx}_{elem}` for arrays
/// - Datatype name for custom datatypes
///
/// Includes depth limit to prevent infinite recursion with nested types.
/// Fix for #822: Array names include element/index sorts to avoid collisions.
/// Fix for #817: Consolidated from chc/mod.rs and statement/sort_inference.rs.
///
/// REQUIRES: `sort` is a valid AY sort.
/// ENSURES: Returned string is non-empty and contains no spaces.
/// ENSURES: Different sorts produce different names (up to depth limit).
pub fn sort_short_name(sort: &ay_bindings::Sort) -> Cow<'static, str> {
    sort_short_name_impl(sort, 0)
}

/// Implementation with depth limit to prevent infinite recursion.
fn sort_short_name_impl(sort: &ay_bindings::Sort, depth: usize) -> Cow<'static, str> {
    use ay_bindings::SortInner;
    const MAX_DEPTH: usize = 3;

    match sort.inner() {
        SortInner::Bool => Cow::Borrowed("bool"),
        SortInner::Int => Cow::Borrowed("int"),
        SortInner::Real => Cow::Borrowed("real"),
        SortInner::BitVec(bv) => match bv.width {
            1 => Cow::Borrowed("bv1"),
            8 => Cow::Borrowed("bv8"),
            16 => Cow::Borrowed("bv16"),
            32 => Cow::Borrowed("bv32"),
            64 => Cow::Borrowed("bv64"),
            128 => Cow::Borrowed("bv128"),
            _ => {
                // non-enum: u32 (bv width)
                let mut name = String::with_capacity(12);
                name.push_str("bv");
                let _ = write!(&mut name, "{}", bv.width);
                Cow::Owned(name)
            }
        },
        SortInner::Array(arr) => {
            // Include element sort in name to avoid collisions (#822)
            if depth < MAX_DEPTH {
                let idx_name = sort_short_name_impl(&arr.index_sort, depth + 1);
                let elem_name = sort_short_name_impl(&arr.element_sort, depth + 1);
                let mut name = String::with_capacity(idx_name.len() + elem_name.len() + 5);
                name.push_str("arr_");
                name.push_str(idx_name.as_ref());
                name.push('_');
                name.push_str(elem_name.as_ref());
                Cow::Owned(name)
            } else {
                Cow::Borrowed("arr")
            }
        }
        SortInner::Datatype(dt) => Cow::Owned(dt.name.clone()),
        SortInner::String => Cow::Borrowed("string"),
        SortInner::FloatingPoint(exp, sig) => {
            let mut name = String::with_capacity(10);
            name.push_str("fp");
            let _ = write!(&mut name, "{}_{}", exp, sig);
            Cow::Owned(name)
        }
        SortInner::Uninterpreted(name) => Cow::Owned(name.clone()),
        SortInner::RegLan => Cow::Borrowed("reglan"),
        _ => Cow::Borrowed("unknown_sort"),
    }
}

// Tests live in trust_mc-compiler (standalone test binaries cannot link rustc sysroot dylibs).
