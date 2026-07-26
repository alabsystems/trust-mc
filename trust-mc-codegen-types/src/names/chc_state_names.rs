// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! CHC encoding variable and memory array names.
//!
//! State variables, memory arrays, heap regions, and allocation-related
//! naming for the CHC encoding. Used across `codegen_decl*`, `heap_state`,
//! `memory_impl*`, and `codegen_expr_env`.
//!
//! Part of #2304, #2408.

use std::borrow::Cow;
use std::fmt::Write as _;
use std::sync::Arc;

/// CHC state variable base name: `_{fn_name}_{local_idx}`.
///
/// The canonical input name for a MIR local in the CHC encoding.
/// Composed with suffix helpers (`addr_name`, `_pointee`, `_len`) for derived vars.
pub fn state_var_name(fn_name: &str, local_idx: usize) -> String {
    let mut s = String::with_capacity(fn_name.len() + 12);
    s.push('_');
    s.push_str(fn_name);
    s.push('_');
    let _ = write!(&mut s, "{local_idx}");
    s
}

/// Pointee variable name: `_{fn_name}_{local_idx}_pointee`.
///
/// Auxiliary state variable for &T/&mut T function arguments (#2496).
/// Single allocation (Part of #2267): inlines `state_var_name` logic.
pub fn pointee_var_name(fn_name: &str, local_idx: usize) -> String {
    let mut s = String::with_capacity(fn_name.len() + 20);
    s.push('_');
    s.push_str(fn_name);
    s.push('_');
    let _ = write!(&mut s, "{local_idx}");
    s.push_str("_pointee");
    s
}

/// CHC output variable name: `{name}__out`.
///
/// In CHC encoding, each state variable `X` has an input version `X` and
/// an output version `X__out` representing the post-transition value.
pub fn out_name(var_name: &str) -> String {
    let mut s = String::with_capacity(var_name.len() + 5);
    s.push_str(var_name);
    s.push_str("__out");
    s
}

/// Combined state variable name pair: `(_{fn_name}_{idx}, _{fn_name}_{idx}__out)`.
///
/// Generates both the input and output CHC state variable names in a single
/// allocation for the base name, then derives the output name from it.
/// Saves one allocation vs calling `state_var_name` + `out_name` separately,
/// since the output name reuses the input name's content. Part of #2267.
pub fn state_var_name_pair(fn_name: &str, local_idx: usize) -> (String, String) {
    let in_name = state_var_name(fn_name, local_idx);
    // Build out_name by extending a copy of in_name — avoids re-formatting the index.
    let mut out = String::with_capacity(in_name.len() + 5);
    out.push_str(&in_name);
    out.push_str("__out");
    (in_name, out)
}

/// Combined state variable + address name: `_{fn_name}_{idx}_addr`.
///
/// Produces the address symbol directly without the intermediate `state_var_name`
/// allocation. Used in heap address assignment where `state_var_name` is only
/// ever consumed by `addr_name`. Part of #2267.
pub fn state_var_addr_name(fn_name: &str, local_idx: usize) -> String {
    let mut s = String::with_capacity(fn_name.len() + 17);
    s.push('_');
    s.push_str(fn_name);
    s.push('_');
    let _ = write!(&mut s, "{local_idx}");
    s.push_str("_addr");
    s
}

/// Static variable name: `_static_{fn_name}_{static_name}`.
///
/// CHC state variable for static/const references (#428).
pub fn static_var_name(fn_name: &str, static_name: &str) -> String {
    let mut s = String::with_capacity(fn_name.len() + static_name.len() + 9);
    s.push_str("_static_");
    s.push_str(fn_name);
    s.push('_');
    s.push_str(static_name);
    s
}

/// Collection length variable name: `{kind}_{fn_name}_len_{local_idx}`.
///
/// Tracks the logical length of HashMap/HashSet locals (#1814).
/// Returns `Arc<str>` — caller stores in `Arc<str>`-keyed collection state (Part of #2267).
pub fn collection_len_var_name(kind: &str, fn_name: &str, local_idx: usize) -> Arc<str> {
    let mut s = String::with_capacity(kind.len() + fn_name.len() + 16);
    s.push_str(kind);
    s.push('_');
    s.push_str(fn_name);
    s.push_str("_len_");
    let _ = write!(&mut s, "{local_idx}");
    Arc::from(s)
}

/// Collection presence-array variable name: `{kind}_{fn_name}_present_{local_idx}`.
///
/// Tracks key membership for HashMap/BTreeMap/TrustMcMap locals in the DT-free
/// parallel-array encoding (Part of #3057). The presence array is
/// `Array(K, Bool)` — maps keys to membership status.
/// Returns `Arc<str>` — caller stores in `Arc<str>`-keyed collection state.
pub fn collection_present_var_name(kind: &str, fn_name: &str, local_idx: usize) -> Arc<str> {
    let mut s = String::with_capacity(kind.len() + fn_name.len() + 16);
    s.push_str(kind);
    s.push('_');
    s.push_str(fn_name);
    s.push_str("_present_");
    let _ = write!(&mut s, "{local_idx}");
    Arc::from(s)
}

/// Collection capacity variable name: `{kind}_{fn_name}_cap_{local_idx}`.
///
/// Tracks the logical capacity of Vec locals (#2877).
/// Returns `Arc<str>` — caller stores in `Arc<str>`-keyed collection state (Part of #2267).
pub fn collection_cap_var_name(kind: &str, fn_name: &str, local_idx: usize) -> Arc<str> {
    let mut s = String::with_capacity(kind.len() + fn_name.len() + 16);
    s.push_str(kind);
    s.push('_');
    s.push_str(fn_name);
    s.push_str("_cap_");
    let _ = write!(&mut s, "{local_idx}");
    Arc::from(s)
}

/// Address symbol name: `{base}_addr`.
///
/// Used for stable address symbols keyed by base name (#1124).
pub fn addr_name(base: &str) -> String {
    let mut s = String::with_capacity(base.len() + 5);
    s.push_str(base);
    s.push_str("_addr");
    s
}

/// Heap region key: `region_{obj_id}`.
///
/// Identifies a heap allocation's typed memory region in the CHC encoding.
///
/// Returns `Cow::Borrowed` for obj_id 0-15 (the common case for small programs),
/// avoiding a `String` allocation per call. Part of #2267.
pub fn region_key(obj_id: u32) -> Cow<'static, str> {
    static NAMES: [&str; 16] = [
        "region_0",
        "region_1",
        "region_2",
        "region_3",
        "region_4",
        "region_5",
        "region_6",
        "region_7",
        "region_8",
        "region_9",
        "region_10",
        "region_11",
        "region_12",
        "region_13",
        "region_14",
        "region_15",
    ];
    if (obj_id as usize) < NAMES.len() {
        Cow::Borrowed(NAMES[obj_id as usize])
    } else {
        let mut s = String::with_capacity(11);
        s.push_str("region_");
        let _ = write!(&mut s, "{obj_id}");
        Cow::Owned(s)
    }
}

/// Type-indexed memory array name: `_{fn_name}_mem_{type_key}`.
///
/// Used for per-type heap memory arrays in the CHC encoding.
/// Returns `Arc<str>` — all callers store the result in `Arc<str>`-keyed maps (Part of #2267).
pub fn mem_array_name(fn_name: &str, type_key: &str) -> Arc<str> {
    let mut s = String::with_capacity(fn_name.len() + type_key.len() + 6);
    s.push('_');
    s.push_str(fn_name);
    s.push_str("_mem_");
    s.push_str(type_key);
    Arc::from(s)
}

/// Combined memory array name pair: `(_{fn}_mem_{key}, _{fn}_mem_{key}__out)`.
///
/// Generates both the input and output CHC memory array names from a single
/// buffer. The `Arc<str>` is created from the base name, then the same buffer
/// is extended with `__out` for the output name — saves one allocation vs
/// calling `mem_array_name` + `out_name` separately. Part of #2267.
pub fn mem_array_name_pair(fn_name: &str, type_key: &str) -> (Arc<str>, String) {
    let base_len = fn_name.len() + type_key.len() + 6;
    let mut s = String::with_capacity(base_len + 5);
    s.push('_');
    s.push_str(fn_name);
    s.push_str("_mem_");
    s.push_str(type_key);
    let in_name: Arc<str> = Arc::from(s.as_str());
    s.push_str("__out");
    (in_name, s)
}

/// Region array name: `_{fn_name}_region_{obj_id}_{type_suffix}`.
///
/// Per-allocation disjoint region arrays for heap modeling (#1443).
/// Returns `Arc<str>` — all callers store the result in `Arc<str>`-keyed maps (Part of #2267).
pub fn region_array_name(fn_name: &str, obj_id: u32, type_suffix: &str) -> Arc<str> {
    let mut s = String::with_capacity(fn_name.len() + type_suffix.len() + 20);
    s.push('_');
    s.push_str(fn_name);
    s.push_str("_region_");
    let _ = write!(&mut s, "{obj_id}");
    s.push('_');
    s.push_str(type_suffix);
    Arc::from(s)
}

/// Combined region array name pair: `(_{fn}_region_{id}_{ty}, _{fn}_region_{id}_{ty}__out)`.
///
/// Generates both input and output region array names from a single buffer.
/// Same optimization as `mem_array_name_pair`. Part of #2267.
pub fn region_array_name_pair(fn_name: &str, obj_id: u32, type_suffix: &str) -> (Arc<str>, String) {
    let mut s = String::with_capacity(fn_name.len() + type_suffix.len() + 25);
    s.push('_');
    s.push_str(fn_name);
    s.push_str("_region_");
    let _ = write!(&mut s, "{obj_id}");
    s.push('_');
    s.push_str(type_suffix);
    let in_name: Arc<str> = Arc::from(s.as_str());
    s.push_str("__out");
    (in_name, s)
}

/// Store coercion symbolic variable: `__store_coerce_{type_key}_{id}`.
///
/// Used for type-coercion symbolics in memory store operations.
pub fn store_coerce_name(type_key: &str, id: u64) -> String {
    let mut s = String::with_capacity(type_key.len() + 24);
    s.push_str("__store_coerce_");
    s.push_str(type_key);
    s.push('_');
    let _ = write!(&mut s, "{id}");
    s
}

/// Allocation object size symbolic: `__alloc_obj_size_{obj_id}`.
///
/// Used to model allocation sizes in heap ops.
pub fn alloc_obj_size_name(obj_id: u32) -> String {
    let mut s = String::with_capacity(24);
    s.push_str("__alloc_obj_size_");
    let _ = write!(&mut s, "{obj_id}");
    s
}

// Tests live in trust_mc-compiler (standalone test binaries cannot link rustc sysroot dylibs).
