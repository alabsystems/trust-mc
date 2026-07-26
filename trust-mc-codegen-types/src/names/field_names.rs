// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! ADT field, constructor, and collection accessor names.
//!
//! Naming for tuple fields, struct fields, enum variant fields,
//! datatype constructors, and discriminant/payload accessors.
//! Used across `aggregate*`, `sort_inference*`, `codegen_types_adt*`,
//! and the place resolution pipeline.
//!
//! Part of #2304, #2408.

use std::borrow::Cow;
use std::fmt::Write as _;

use ay_bindings::Sort;

/// Tuple field names for common indices (0-15), avoiding `format!` allocation.
///
/// Returns `Cow::Borrowed("fld_N")` for indices 0-15 (the common case for Rust
/// tuples and struct aggregates), falling back to a dynamically formatted owned
/// string for larger indices.
pub fn tuple_field_name(index: usize) -> Cow<'static, str> {
    static NAMES: [&str; 16] = [
        "fld_0", "fld_1", "fld_2", "fld_3", "fld_4", "fld_5", "fld_6", "fld_7", "fld_8", "fld_9",
        "fld_10", "fld_11", "fld_12", "fld_13", "fld_14", "fld_15",
    ];
    if index < NAMES.len() {
        Cow::Borrowed(NAMES[index])
    } else {
        let mut name = String::with_capacity(24);
        name.push_str("fld_");
        let _ = write!(&mut name, "{index}");
        Cow::Owned(name)
    }
}

/// Format an ADT struct field name: `fld_{name}`.
pub fn adt_struct_field_name(name: &str) -> String {
    let mut field_name = String::with_capacity(name.len() + 4);
    field_name.push_str("fld_");
    field_name.push_str(name);
    field_name
}

/// Format an enum variant field name: `{variant}_field_{idx}`.
pub fn variant_field_name(variant: &str, idx: usize) -> String {
    let mut field_name = String::with_capacity(variant.len() + 27);
    field_name.push_str(variant);
    field_name.push_str("_field_");
    let _ = write!(&mut field_name, "{idx}");
    field_name
}

/// Indexed field access name: `{base}_field_{idx}`.
///
/// Used for struct field projections where the field is identified by index
/// rather than by name.
pub fn indexed_field_name(base: &str, idx: usize) -> String {
    let mut field_name = String::with_capacity(base.len() + 27);
    field_name.push_str(base);
    field_name.push_str("_field_");
    let _ = write!(&mut field_name, "{idx}");
    field_name
}

/// Coroutine root field name for the direct/top-level view.
#[must_use]
pub fn coroutine_direct_fields_name() -> &'static str {
    "direct_fields"
}

/// Coroutine discriminant field name inside the direct-fields view.
#[must_use]
pub fn coroutine_discriminant_field_name() -> &'static str {
    "case"
}

/// Coroutine variant root field name: `coroutine_variant_{variant_name}`.
pub fn coroutine_variant_field_name(variant_name: &str) -> String {
    let mut field_name = String::with_capacity(variant_name.len() + 18);
    field_name.push_str("coroutine_variant_");
    field_name.push_str(variant_name);
    field_name
}

/// Prefix shared by [`coroutine_field_name`] and [`coroutine_field_index`].
const COROUTINE_FIELD_PREFIX: &str = "coroutine_field_";

/// Coroutine nested field name: `coroutine_field_{idx}`.
pub fn coroutine_field_name(idx: usize) -> String {
    let mut field_name = String::with_capacity(24);
    field_name.push_str(COROUTINE_FIELD_PREFIX);
    let _ = write!(&mut field_name, "{idx}");
    field_name
}

/// Inverse of [`coroutine_field_name`]: recover the MIR field index encoded in
/// a coroutine view field name (`coroutine_field_{idx}` → `idx`).
///
/// Coroutine view datatypes order their fields by increasing byte OFFSET
/// (`build_view_info`), not by MIR field index — the index survives only in
/// the field NAME. Positional access on these views silently reads the wrong
/// slot whenever offset order differs from index order, so consumers must map
/// through this helper (or select by name) instead.
///
/// Returns `None` for the discriminant field (`case`), variant/root view
/// fields, and any other name that does not encode an index.
#[must_use]
pub fn coroutine_field_index(name: &str) -> Option<usize> {
    name.strip_prefix(COROUTINE_FIELD_PREFIX)?.parse().ok()
}

/// Enum variant indexed field access: `{base}_variant_{variant_idx}_field_{field_idx}`.
///
/// Used for accessing fields within a specific enum variant's data, qualified
/// by the base variable name. Distinct from `variant_field_name` which uses
/// variant name (not index).
pub fn base_variant_field_name(base: &str, variant_idx: usize, field_idx: usize) -> String {
    let mut field_name = String::with_capacity(base.len() + 48);
    field_name.push_str(base);
    field_name.push_str("_variant_");
    let _ = write!(&mut field_name, "{variant_idx}");
    field_name.push_str("_field_");
    let _ = write!(&mut field_name, "{field_idx}");
    field_name
}

/// Datatype constructor name: `{name}_mk`.
///
/// The `_mk` suffix is the SMT convention for datatype constructors.
/// Used in ~40 sites across the codebase wherever a datatype needs construction.
pub fn cons_name(sort_name: &str) -> String {
    let mut s = String::with_capacity(sort_name.len() + 3);
    s.push_str(sort_name);
    s.push_str("_mk");
    s
}

/// Resolve the default constructor name for a datatype sort, falling back to `<sort_name>_mk`.
///
/// Returns the sort's first constructor name if present, otherwise synthesizes `<sort_name>_mk`.
/// Produces an owned `String` because callers typically move the Sort into the same
/// `Expr::datatype_constructor` call, which would conflict with a borrow-based return.
pub fn resolve_ctor_name(sort: &Sort, fallback_sort_name: &str) -> String {
    sort.datatype_default_constructor().map_or_else(|| cons_name(fallback_sort_name), str::to_owned)
}

/// Discriminant (first-element) access name: `{base}.0`.
///
/// Used for Option/Result discriminant access and checked-arithmetic overflow
/// flag access.
pub fn discrim_name(base: &str) -> String {
    let mut s = String::with_capacity(base.len() + 2);
    s.push_str(base);
    s.push_str(".0");
    s
}

/// Value (second-element) access name: `{base}.1`.
///
/// Used for Option/Result payload access and checked-arithmetic result access.
pub fn payload_name(base: &str) -> String {
    let mut s = String::with_capacity(base.len() + 2);
    s.push_str(base);
    s.push_str(".1");
    s
}

/// Collection length variable name: `{base}_len`.
///
/// Tracks the logical length of collection stubs (Vec, HashSet, BTreeSet, String).
pub fn len_name(base: &str) -> String {
    let mut s = String::with_capacity(base.len() + 4);
    s.push_str(base);
    s.push_str("_len");
    s
}

/// Metadata symbol name: `{base}_meta`.
///
/// Used for fat pointer metadata symbols (#1129).
pub fn meta_name(base: &str) -> String {
    let mut s = String::with_capacity(base.len() + 5);
    s.push_str(base);
    s.push_str("_meta");
    s
}

// Tests live in trust_mc-compiler (standalone test binaries cannot link rustc sysroot dylibs).
