// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Shared sort constructors: field layout builders for collection and enum sorts.
//!
//! Eliminates duplicate literal String field allocations across sort_inference_adt.rs
//! and codegen_types_adt_sort.rs.
//!
//! Extracted from names.rs — Part of #2267, #2408.

use std::borrow::Cow;

use crate::types::ptr_sort;
use ay_bindings::Sort;

/// Create a struct sort from borrowed field names.
///
/// Wraps [`Sort::struct_type`] converting `Into<String>` field names to owned
/// `String`s as required by the upstream `ay-bindings` API at the pinned rev.
#[must_use]
pub fn struct_sort(
    name: impl Into<String>,
    fields: impl IntoIterator<Item = (impl Into<String>, Sort)>,
) -> Sort {
    let owned: Vec<(String, Sort)> = fields.into_iter().map(|(n, s)| (n.into(), s)).collect();
    Sort::struct_type(name, owned)
}

/// Create an enum (datatype) sort from borrowed variant/field names.
///
/// Wraps [`Sort::enum_type`] converting `Into<String>` names to owned
/// `String`s, mirroring the `struct_sort` pattern above.
#[must_use]
pub fn enum_sort<V, F>(
    name: impl Into<String>,
    variants: impl IntoIterator<Item = (V, impl IntoIterator<Item = (F, Sort)>)>,
) -> Sort
where
    V: Into<String>,
    F: Into<String>,
{
    let owned: Vec<(String, Vec<(String, Sort)>)> = variants
        .into_iter()
        .map(|(v, fields)| {
            let fs: Vec<(String, Sort)> = fields.into_iter().map(|(n, s)| (n.into(), s)).collect();
            (v.into(), fs)
        })
        .collect();
    Sort::enum_type(name, owned)
}

/// SMT datatype name for Rust `String`.
///
/// Z3's built-in string theory (enabled under `(set-logic ALL)`) reserves the bare name `String`.
/// Using `RustString` avoids the collision while keeping sort semantics identical.
/// See #2253.
pub const RUST_STRING_SORT: &str = "RustString";

/// SMT datatype constructor name for Rust `String`.
pub const RUST_STRING_CONS: &str = "RustString_mk";

/// String struct fields: `(fld_ptr, fld_len, fld_cap)`.
///
/// Used for `std::string::String` which is a `Vec<u8>` wrapper without
/// the explicit data array field (data is accessed via pointer).
pub fn string_fields() -> Vec<(&'static str, Sort)> {
    vec![("fld_ptr", ptr_sort()), ("fld_len", ptr_sort()), ("fld_cap", ptr_sort())]
}

/// Vec Datatype field names — single source of truth for all field-name
/// string literals and positional indices used by both name-based
/// (`ChcVecFields::extract`) and index-based (`extract_projected_vec_fields`)
/// access paths.  Part of #2931.
pub mod vec_layout {
    /// Field name for the heap pointer.
    pub const FLD_PTR: &str = "fld_ptr";
    /// Field name for the tracked length.
    pub const FLD_LEN: &str = "fld_len";
    /// Field name for the allocated capacity.
    pub const FLD_CAP: &str = "fld_cap";
    /// Field name for the backing data array.
    pub const FLD_DATA: &str = "fld_data";

    /// Positional index of `fld_ptr` in the Vec flattened projection.
    pub const IDX_PTR: usize = 0;
    /// Positional index of `fld_len` in the Vec flattened projection.
    pub const IDX_LEN: usize = 1;
    /// Positional index of `fld_cap` in the Vec flattened projection.
    pub const IDX_CAP: usize = 2;
    /// Positional index of `fld_data` in the Vec flattened projection.
    pub const IDX_DATA: usize = 3;
    /// Total number of fields in a Vec Datatype.
    pub const FIELD_COUNT: usize = 4;

    /// Field names in positional order (index-aligned with the `IDX_*` constants).
    pub const FIELDS_ORDERED: [&str; FIELD_COUNT] = [FLD_PTR, FLD_LEN, FLD_CAP, FLD_DATA];
}

/// Vec-like struct fields: `(fld_ptr, fld_len, fld_cap, fld_data)`.
pub fn vec_fields(data_sort: Sort) -> Vec<(&'static str, Sort)> {
    use vec_layout::{FIELD_COUNT, FIELDS_ORDERED, FLD_CAP, FLD_DATA, FLD_LEN, FLD_PTR};
    let fields = vec![
        (FLD_PTR, ptr_sort()),
        (FLD_LEN, ptr_sort()),
        (FLD_CAP, ptr_sort()),
        (FLD_DATA, data_sort),
    ];
    // Cross-validate field count and name order against vec_layout constants.
    debug_assert_eq!(fields.len(), FIELD_COUNT, "vec_fields / FIELD_COUNT mismatch");
    debug_assert!(
        fields.iter().zip(FIELDS_ORDERED.iter()).all(|((n, _), c)| n == c),
        "vec_fields name order differs from FIELDS_ORDERED"
    );
    fields
}

/// VecIntoIter struct fields for CHC path: `(fld_vec, fld_pos)`.
///
/// The CHC path uses a 2-field logical model where fld_vec holds the entire Vec
/// Datatype and fld_pos is an index counter. This is suitable for CHC/Horn clause
/// generation where the abstract model is controlled by stubs.
pub fn vec_into_iter_fields(vec_sort: Sort) -> Vec<(&'static str, Sort)> {
    vec![("fld_vec", vec_sort), ("fld_pos", ptr_sort())]
}

/// VecIntoIter struct fields for BMC path: 6 fields matching MIR layout.
///
/// Part of #2912: rustc inlines `IntoIter::next()` and other methods, producing
/// MIR that accesses the real `std::vec::IntoIter<T>` field layout:
///
/// | MIR idx | Rust field          | AY model         |
/// |---------|---------------------|------------------|
/// | 0       | buf: NonNull<T>     | fld_buf: bv64    |
/// | 1       | phantom: PhantomData| fld_phantom: Bool |
/// | 2       | cap: usize          | fld_cap: bv64    |
/// | 3       | alloc: ManuallyDrop | fld_alloc: Bool   |
/// | 4       | ptr: NonNull<T>     | fld_ptr: bv64    |
/// | 5       | end: *const T       | fld_end: bv64    |
///
/// The inlined `next()` compares fld_ptr with fld_end to determine exhaustion.
/// Without 6 fields, field projections on indices 2-5 fail with "out of bounds".
#[must_use]
pub fn vec_into_iter_bmc_fields() -> Vec<(&'static str, Sort)> {
    vec![
        ("fld_buf", ptr_sort()),
        ("fld_phantom", Sort::bool()),
        ("fld_cap", ptr_sort()),
        ("fld_alloc", Sort::bool()),
        ("fld_ptr", ptr_sort()),
        ("fld_end", ptr_sort()),
    ]
}

/// IndexRange struct sort: `{ fld_start: bvN, fld_end: bvN }`.
#[must_use]
pub fn index_range_sort() -> Sort {
    struct_sort("IndexRange", [("fld_start", ptr_sort()), ("fld_end", ptr_sort())])
}

/// Option empty-variant constructor name scoped to a concrete datatype sort.
///
/// Example: `None_Option_bv32`.
pub fn option_none_constructor_name(option_sort_name: &str) -> String {
    let mut name = String::with_capacity(option_sort_name.len() + 5);
    name.push_str("None_");
    name.push_str(option_sort_name);
    name
}

/// Option payload-variant constructor name scoped to a concrete datatype sort.
///
/// Example: `Some_Option_bv32`.
pub fn option_some_constructor_name(option_sort_name: &str) -> String {
    let mut name = String::with_capacity(option_sort_name.len() + 5);
    name.push_str("Some_");
    name.push_str(option_sort_name);
    name
}

/// Returns true when `name` denotes an Option payload constructor.
///
/// Accepts both legacy bare names (`Some`) and scoped names (`Some_Option_bv32`).
pub fn is_some_constructor(name: &str) -> bool {
    name == "Some" || name.starts_with("Some_")
}

/// Returns true when `name` denotes an Option empty constructor.
///
/// Accepts both legacy bare names (`None`) and scoped names (`None_Option_bv32`).
pub fn is_none_constructor(name: &str) -> bool {
    name == "None" || name.starts_with("None_")
}

/// Option-like enum constructors scoped to a concrete datatype sort.
///
/// This avoids global constructor-name collisions when multiple Option
/// instantiations are declared in one SMT program (for example `Option_bv32`
/// and `Option_bv64`), which otherwise share bare `Some`/`None`.
///
/// Part of #3945: accessor names are also scoped (`value_Option_bv64`)
/// because Z3 PDR cannot disambiguate overloaded accessor names across
/// multiple datatypes.
pub fn option_constructors(
    option_sort_name: &str,
    payload_sort: Sort,
) -> Vec<(String, Vec<(String, Sort)>)> {
    vec![
        (self::option_none_constructor_name(option_sort_name), vec![]),
        (
            self::option_some_constructor_name(option_sort_name),
            vec![(option_value_field_name(option_sort_name), payload_sort)],
        ),
    ]
}

/// Returns the scoped accessor name for an Option's payload field.
///
/// Part of #3945: Z3 PDR fails with "Uninterpreted 'value' in <null>"
/// when multiple datatypes declare a `value` accessor. Scoping the name
/// to the option sort (`value_Option_bv64`) avoids the collision.
pub fn option_value_field_name(option_sort_name: &str) -> String {
    format!("value_{option_sort_name}")
}

/// Scope an enum constructor name to its datatype sort.
///
/// Returns the scoped name for all enum constructors:
/// - `Some` -> `Some_<sort>`, `None` -> `None_<sort>` (Option, Part of #2549)
/// - `Ok` -> `Ok_<sort>`, `Err` -> `Err_<sort>` (Result, Part of #2631)
/// - General variants: `<Name>` -> `<Name>_<sort>` (Part of #3041)
///
/// Scoping all constructor names avoids Z3 "ambiguous function declaration
/// reference" errors when multiple enums in the same program share variant
/// names (e.g., two enums both having `One` / `Two`).
pub fn scope_option_ctor<'a>(raw: impl Into<Cow<'a, str>>, sort_name: &str) -> String {
    let raw = raw.into();
    if is_some_constructor(&raw) {
        option_some_constructor_name(sort_name)
    } else if is_none_constructor(&raw) {
        option_none_constructor_name(sort_name)
    } else if is_ok_constructor(&raw) {
        result_ok_constructor_name(sort_name)
    } else if is_err_constructor(&raw) {
        result_err_constructor_name(sort_name)
    } else {
        // Part of #3041: Scope all enum constructor names to the datatype
        // sort name to prevent Z3 ambiguity across enums sharing variant names.
        let mut name = String::with_capacity(raw.len() + 1 + sort_name.len());
        name.push_str(&raw);
        name.push('_');
        name.push_str(sort_name);
        name
    }
}

/// Result Ok-variant constructor name scoped to a concrete datatype sort.
///
/// Example: `Ok_Result_bv32_String`.
/// Part of #2631.
pub fn result_ok_constructor_name(result_sort_name: &str) -> String {
    let mut name = String::with_capacity(result_sort_name.len() + 3);
    name.push_str("Ok_");
    name.push_str(result_sort_name);
    name
}

/// Result Err-variant constructor name scoped to a concrete datatype sort.
///
/// Example: `Err_Result_bv32_String`.
/// Part of #2631.
pub fn result_err_constructor_name(result_sort_name: &str) -> String {
    let mut name = String::with_capacity(result_sort_name.len() + 4);
    name.push_str("Err_");
    name.push_str(result_sort_name);
    name
}

/// Returns true when `name` denotes a Result Ok constructor.
///
/// Accepts both legacy bare names (`Ok`) and scoped names (`Ok_Result_bv32`).
/// Part of #2631.
pub fn is_ok_constructor(name: &str) -> bool {
    name == "Ok" || name.starts_with("Ok_")
}

/// Returns true when `name` denotes a Result Err constructor.
///
/// Accepts both legacy bare names (`Err`) and scoped names (`Err_Result_bv32`).
/// Part of #2631.
pub fn is_err_constructor(name: &str) -> bool {
    name == "Err" || name.starts_with("Err_")
}

/// HashSet iterator struct fields: `(fld_set, fld_keys, fld_pos, fld_len)`.
pub fn hashset_iter_fields(set_sort: Sort, keys_sort: Sort) -> Vec<(&'static str, Sort)> {
    vec![
        ("fld_set", set_sort),
        ("fld_keys", keys_sort),
        ("fld_pos", ptr_sort()),
        ("fld_len", ptr_sort()),
    ]
}

/// HashMap iterator struct fields: `(fld_data, fld_present, fld_keys, fld_pos, fld_len)`.
///
/// Part of #3057: DT-free parallel-array encoding. The iterator carries both
/// the data array `Array(K, V)` and the presence array `Array(K, Bool)`.
pub fn hashmap_iter_fields(
    data_sort: Sort,
    present_sort: Sort,
    keys_sort: Sort,
) -> Vec<(&'static str, Sort)> {
    vec![
        ("fld_data", data_sort),
        ("fld_present", present_sort),
        ("fld_keys", keys_sort),
        ("fld_pos", ptr_sort()),
        ("fld_len", ptr_sort()),
    ]
}

/// RawVec struct fields: `(fld_ptr, fld_cap)`.
pub fn rawvec_fields() -> Vec<(&'static str, Sort)> {
    vec![("fld_ptr", ptr_sort()), ("fld_cap", ptr_sort())]
}

/// Layout struct fields: `(fld_size, fld_align)`.
pub fn layout_fields() -> Vec<(&'static str, Sort)> {
    vec![("fld_size", ptr_sort()), ("fld_align", ptr_sort())]
}

/// BTreeMap entry struct fields: `(fld_key, fld_map)`.
///
/// Shared by VacantEntry and OccupiedEntry sorts.
pub fn btree_entry_fields() -> Vec<(&'static str, Sort)> {
    vec![("fld_key", ptr_sort()), ("fld_map", ptr_sort())]
}

// Tests live in trust_mc-compiler (standalone test binaries cannot link rustc sysroot dylibs).
