// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Shared store coercion for array stores.
//!
//! Part of #2894: moves Vec/String-specific coercion out of
//! `ay_bindings::Expr::store()` into the compiler codegen layer
//! where trust_mc-specific datatype layout decisions belong.
//!
//! Part of #2970: adds `coerce_store_value_bmc()` for BMC-path sort
//! coercion beyond Vec/String (BV width, Bool↔BV, Int↔BV, Datatype→BV).
//!
//! Used by both CHC and statement codegen paths.

use std::sync::atomic::{AtomicU64, Ordering};

use ay_bindings::{Expr, Sort};

use crate::codegen_ay::names;
use crate::codegen_ay::types::{
    POINTER_WIDTH, SignExtension, coerce_bitvec_width_safe, flatten_datatype_to_bitvec,
};

/// Counter for BMC store coercion fresh-symbolic fallbacks (Part of #2970).
pub(super) static BMC_STORE_COERCION_FALLBACK: AtomicU64 = AtomicU64::new(0);

/// Take (consume) the BMC store coercion fallback count for unsoundness reporting (#3064).
pub(super) fn take_bmc_store_coercion_fallback_count() -> usize {
    BMC_STORE_COERCION_FALLBACK.swap(0, Ordering::Relaxed) as usize
}

/// Non-destructive read of the BMC store coercion fallback counter (Part of #3064).
pub(in crate::codegen_ay) fn get_bmc_store_coercion_fallback_count() -> usize {
    BMC_STORE_COERCION_FALLBACK.load(Ordering::Relaxed) as usize
}

/// Set BMC store coercion fallback counter for test isolation (Part of #3369).
#[cfg(test)]
#[allow(dead_code)]
pub(in crate::codegen_ay) fn set_bmc_store_coercion_fallback_count_for_test(count: u64) {
    BMC_STORE_COERCION_FALLBACK.store(count, Ordering::Relaxed);
}

/// Coerce a value to match an array's element sort for Vec/String↔BitVec cases.
///
/// This handles the trust_mc-specific coercion that was previously embedded in
/// `ay_bindings::Expr::store()`:
///
/// - BitVec(POINTER_WIDTH) → Vec/String datatype (wraps as {ptr, 0, 0[, data]})
/// - Vec/String datatype → BitVec(POINTER_WIDTH) (extracts fld_ptr)
///
/// Returns `None` if no Vec/String coercion applies (caller should pass
/// the value through to `Expr::store()` which handles SMT-generic coercions).
#[must_use]
pub(super) fn coerce_vec_string_store_value(arr_sort: &Sort, value: &Expr) -> Option<Expr> {
    let arr = arr_sort.array_sort()?;
    let elem_sort = &arr.element_sort;
    let val_sort = value.sort();

    // Already matching — no coercion needed.
    if *val_sort == *elem_sort {
        return None;
    }

    // Case 1: Array expects Vec/String datatype, value is pointer-width BitVec.
    // Wrap the BitVec as the ptr field with zero len/cap (and symbolic data for Vec).
    if let Some(dt_name) = elem_sort.datatype_name()
        && is_vec_or_string_name(dt_name)
        && val_sort.is_bitvec()
        && val_sort.bitvec_width() == Some(POINTER_WIDTH)
    {
        return coerce_bitvec_to_vec_string(dt_name, elem_sort, value);
    }

    // Case 2: Array expects pointer-width BitVec, value is Vec/String datatype.
    // Extract fld_ptr from the datatype.
    if elem_sort.is_bitvec()
        && elem_sort.bitvec_width() == Some(POINTER_WIDTH)
        && let Some(dt_name) = val_sort.datatype_name()
        && is_vec_or_string_name(dt_name)
    {
        return coerce_vec_string_to_bitvec(dt_name, elem_sort, value);
    }

    None
}

/// Check if a datatype name is a Vec or String variant that we should coerce.
///
/// Accepts both current names (`RustString`, `Vec_*`) and legacy names
/// (`String`, `Vec`) for backwards compatibility during migration.
fn is_vec_or_string_name(name: &str) -> bool {
    name == names::RUST_STRING_SORT || name == "String" || name == "Vec" || name.starts_with("Vec_")
}

/// Coerce pointer-width BitVec → Vec/String datatype.
///
/// Constructs {ptr=value, len=0, cap=0} for String-like types (3 fields),
/// or {ptr=value, len=0, cap=0, data=symbolic} for Vec-like types (4 fields).
fn coerce_bitvec_to_vec_string(dt_name: &str, target_sort: &Sort, value: &Expr) -> Option<Expr> {
    let ptr_sort = datatype_field_sort(target_sort, "fld_ptr")?;
    if ptr_sort != *value.sort() {
        return None;
    }

    let len_sort = datatype_field_sort(target_sort, "fld_len")?;
    let cap_sort = datatype_field_sort(target_sort, "fld_cap")?;

    let len = zero_expr_for_sort(&len_sort)?;
    let cap = zero_expr_for_sort(&cap_sort)?;

    let cons = names::cons_name(dt_name);

    // Check if this datatype has a fld_data field (Vec has 4 fields, String has 3).
    if let Some(data_sort) = datatype_field_sort(target_sort, "fld_data") {
        // Vec-like: 4 fields. Use a constant array of zeros for the data field.
        let data = if let Some(arr) = data_sort.array_sort() {
            let zero = zero_expr_for_sort(&arr.element_sort)
                .unwrap_or_else(|| Expr::bitvec_const(0u64, 8));
            Expr::const_array(arr.index_sort.clone(), zero)
        } else {
            // fld_data is not an array — unexpected layout, bail.
            return None;
        };
        Some(Expr::datatype_constructor(
            dt_name,
            cons,
            vec![value.clone(), len, cap, data],
            target_sort.clone(),
        ))
    } else {
        // String-like: 3 fields (fld_ptr, fld_len, fld_cap).
        Some(Expr::datatype_constructor(
            dt_name,
            cons,
            vec![value.clone(), len, cap],
            target_sort.clone(),
        ))
    }
}

/// Coerce Vec/String datatype → pointer-width BitVec by extracting fld_ptr.
fn coerce_vec_string_to_bitvec(dt_name: &str, target_sort: &Sort, value: &Expr) -> Option<Expr> {
    let ptr_sort = datatype_field_sort(value.sort(), "fld_ptr")?;
    if ptr_sort != *target_sort {
        return None;
    }
    Some(value.clone().field_select(dt_name, "fld_ptr", target_sort.clone()))
}

/// Look up a named field's sort within a datatype sort.
fn datatype_field_sort(sort: &Sort, field_name: &str) -> Option<Sort> {
    let dt = sort.datatype_sort()?;
    dt.constructors.iter().find_map(|constructor| {
        constructor
            .fields
            .iter()
            .find(|field| field.name == field_name)
            .map(|field| field.sort.clone())
    })
}

/// Create a zero-valued expression for numeric sorts.
fn zero_expr_for_sort(sort: &Sort) -> Option<Expr> {
    if sort.is_bitvec() {
        Some(Expr::bitvec_const(0u64, sort.bitvec_width()?))
    } else if sort.is_int() {
        Some(Expr::int_const(0))
    } else {
        None
    }
}

/// Attempt sort coercion for a BMC store value beyond Vec/String cases.
///
/// Part of #2970: The BMC path only had Vec/String coercion via
/// `coerce_vec_string_store_value()`. When the ay bump added strict sort
/// validation, non-Vec/String mismatches (e.g., struct Datatype vs BV)
/// caused panics. This function handles the additional coercion cases
/// that the CHC path's `coerce_store_value()` covers:
///
/// - BV width mismatch (zero-extend or truncate)
/// - Bool ↔ BV conversion
/// - Int ↔ BV conversion
/// - Datatype → BV flattening (single-constructor structs, option-like enums)
///
/// Returns `Some(coerced)` if coercion succeeded, `None` if the sorts
/// already match or coercion is not possible (caller must create a
/// fresh symbolic via its own context as last-resort fallback).
/// Part of #2976: `signed` controls whether BV widening uses sign-extend
/// (true) or zero-extend (false). Callers should derive signedness from
/// the source MIR type via `ty_signedness_shallow`.
#[must_use]
pub(super) fn coerce_store_value_bmc(arr_sort: &Sort, value: &Expr, signed: bool) -> Option<Expr> {
    let arr = arr_sort.array_sort()?;
    let elem_sort = &arr.element_sort;
    let val_sort = value.sort();

    // Already matching — no coercion needed.
    if *val_sort == *elem_sort {
        return None;
    }

    // BV width mismatch: extend or truncate to target width.
    if val_sort.is_bitvec() && elem_sort.is_bitvec() {
        if let Some(target_w) = elem_sort.bitvec_width() {
            let ext = SignExtension::for_signedness(signed);
            return Some(coerce_bitvec_width_safe(value.clone(), target_w, ext));
        }
    }

    // Bool → BV: true→1, false→0 at target width.
    if val_sort.is_bool() && elem_sort.is_bitvec() {
        if let Some(target_w) = elem_sort.bitvec_width() {
            return Some(Expr::ite(
                value.clone(),
                Expr::bitvec_const(1u64, target_w),
                Expr::bitvec_const(0u64, target_w),
            ));
        }
    }

    // BV → Bool: nonzero→true, zero→false.
    if val_sort.is_bitvec() && elem_sort.is_bool() {
        if let Some(w) = val_sort.bitvec_width() {
            return Some(value.clone().ne(Expr::bitvec_const(0u64, w)));
        }
    }

    // Int → BV: integer to bitvector conversion.
    if val_sort.is_int() && elem_sort.is_bitvec() {
        if let Some(target_w) = elem_sort.bitvec_width() {
            return Some(value.clone().int2bv(target_w));
        }
    }

    // BV → Int: use signed/unsigned conversion based on source type.
    // Part of #3055: was unconditionally bv2int_signed(), now respects caller-provided signedness.
    if val_sort.is_bitvec() && elem_sort.is_int() {
        let v = value.clone();
        return Some(if signed { v.bv2int_signed() } else { v.bv2int() });
    }

    // Datatype → BV: flatten struct/enum fields to concatenated bitvector.
    if val_sort.is_datatype() && elem_sort.is_bitvec() {
        if let Some(target_w) = elem_sort.bitvec_width() {
            if let Some(flat) = flatten_datatype_to_bitvec(value, target_w) {
                return Some(flat);
            }
        }
    }

    // BV → Datatype: unflatten bitvec back to struct/enum (Part of dterm#6841).
    // Inverse of Datatype → BV above. Needed when codegen produces a bitvec
    // operand (e.g., partial field) but the array expects a Datatype element.
    if val_sort.is_bitvec() && elem_sort.is_datatype() {
        if let Some(unflat) =
            trust_mc_codegen_types::types::unflatten_bitvec_to_datatype(value, elem_sort)
        {
            return Some(unflat);
        }
    }

    // No coercion possible — caller must create fresh symbolic.
    None
}

/// Generate a unique name for a BMC store coercion fresh-symbolic variable.
///
/// Part of #2970: Used by BMC store sites as last-resort fallback when
/// `coerce_store_value_bmc()` returns `None` and sorts still mismatch.
pub(super) fn bmc_store_fallback_name() -> String {
    use std::fmt::Write;
    let id = BMC_STORE_COERCION_FALLBACK.fetch_add(1, Ordering::Relaxed);
    let mut name = String::with_capacity(24);
    name.push_str("__bmc_store_coercion_");
    let _ = write!(name, "{id}");
    name
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::codegen_ay::names::struct_sort;
    use crate::codegen_ay::types::{bool_sort, int_sort, ptr_sort};

    #[test]
    fn test_bitvec_to_vec_coercion() {
        let ptr_sort = ptr_sort();
        let data_sort = Sort::array(ptr_sort.clone(), Sort::bitvec(32));
        let vec_sort = struct_sort(
            "Vec",
            [
                ("fld_ptr", ptr_sort.clone()),
                ("fld_len", ptr_sort.clone()),
                ("fld_cap", ptr_sort.clone()),
                ("fld_data", data_sort),
            ],
        );
        let arr_sort = Sort::array(ptr_sort.clone(), vec_sort);
        let value = Expr::var("ptr", ptr_sort);

        let coerced =
            coerce_vec_string_store_value(&arr_sort, &value).expect("should coerce BitVec to Vec");
        let s = coerced.to_string();
        assert!(s.contains("Vec_mk"), "should use Vec_mk constructor: {s}");
        assert!(s.contains("ptr"), "should contain ptr: {s}");
    }

    #[test]
    fn test_bitvec_to_string_coercion() {
        let ptr_sort = ptr_sort();
        let string_sort = struct_sort(
            names::RUST_STRING_SORT,
            [
                ("fld_ptr", ptr_sort.clone()),
                ("fld_len", ptr_sort.clone()),
                ("fld_cap", ptr_sort.clone()),
            ],
        );
        let arr_sort = Sort::array(ptr_sort.clone(), string_sort);
        let value = Expr::var("ptr", ptr_sort);

        let coerced = coerce_vec_string_store_value(&arr_sort, &value)
            .expect("should coerce BitVec to RustString");
        let s = coerced.to_string();
        assert!(s.contains("RustString_mk"), "should use RustString_mk: {s}");
    }

    #[test]
    fn test_vec_to_bitvec_coercion() {
        let ptr_sort = ptr_sort();
        let vec_sort = struct_sort(
            "Vec",
            [
                ("fld_ptr", ptr_sort.clone()),
                ("fld_len", ptr_sort.clone()),
                ("fld_cap", ptr_sort.clone()),
            ],
        );
        let arr_sort = Sort::array(ptr_sort.clone(), ptr_sort);
        let value = Expr::var("vec_val", vec_sort);

        let coerced =
            coerce_vec_string_store_value(&arr_sort, &value).expect("should coerce Vec to BitVec");
        let s = coerced.to_string();
        assert!(s.contains("fld_ptr"), "should extract fld_ptr: {s}");
    }

    #[test]
    fn test_no_coercion_for_matching_sorts() {
        let ptr_sort = ptr_sort();
        let arr_sort = Sort::array(ptr_sort.clone(), ptr_sort.clone());
        let value = Expr::var("v", ptr_sort);

        assert!(coerce_vec_string_store_value(&arr_sort, &value).is_none());
    }

    #[test]
    fn test_no_coercion_for_non_vec_string() {
        let ptr_sort = ptr_sort();
        let custom_sort = struct_sort(
            "MyStruct",
            [
                ("fld_ptr", ptr_sort.clone()),
                ("fld_len", ptr_sort.clone()),
                ("fld_cap", ptr_sort.clone()),
            ],
        );
        let arr_sort = Sort::array(ptr_sort.clone(), custom_sort);
        let value = Expr::var("ptr", ptr_sort);

        assert!(
            coerce_vec_string_store_value(&arr_sort, &value).is_none(),
            "should not coerce for non-Vec/String types"
        );
    }

    #[test]
    fn test_no_coercion_for_wrong_width() {
        let ptr_sort = ptr_sort();
        let vec_sort = struct_sort(
            "Vec",
            [
                ("fld_ptr", ptr_sort.clone()),
                ("fld_len", ptr_sort.clone()),
                ("fld_cap", ptr_sort.clone()),
            ],
        );
        let arr_sort = Sort::array(ptr_sort, vec_sort);
        let value = Expr::var("small", Sort::bv32());

        assert!(
            coerce_vec_string_store_value(&arr_sort, &value).is_none(),
            "should not coerce non-pointer-width BitVec"
        );
    }

    #[test]
    fn test_legacy_string_name_accepted() {
        let ptr_sort = ptr_sort();
        let string_sort = struct_sort(
            "String",
            [
                ("fld_ptr", ptr_sort.clone()),
                ("fld_len", ptr_sort.clone()),
                ("fld_cap", ptr_sort.clone()),
            ],
        );
        let arr_sort = Sort::array(ptr_sort.clone(), string_sort);
        let value = Expr::var("ptr", ptr_sort);

        let result = coerce_vec_string_store_value(&arr_sort, &value);
        assert!(result.is_some(), "should accept legacy 'String' name");
    }

    // --- coerce_store_value_bmc tests (Part of #2970) ---

    #[test]
    fn test_bmc_coerce_bv_width_mismatch() {
        // Array expects BV64, value is BV32 → should zero-extend.
        let arr_sort = Sort::array(ptr_sort(), Sort::bitvec(64));
        let value = Expr::var("v32", Sort::bv32());
        let coerced =
            coerce_store_value_bmc(&arr_sort, &value, false).expect("should coerce BV32→BV64");
        assert_eq!(coerced.sort().bitvec_width(), Some(64), "coerced value should be BV64");
    }

    #[test]
    fn test_bmc_coerce_bool_to_bv() {
        // Array expects BV8, value is Bool → should convert via ITE.
        let arr_sort = Sort::array(ptr_sort(), Sort::bitvec(8));
        let value = Expr::var("flag", bool_sort());
        let coerced =
            coerce_store_value_bmc(&arr_sort, &value, false).expect("should coerce Bool→BV8");
        assert_eq!(coerced.sort().bitvec_width(), Some(8), "coerced value should be BV8");
    }

    #[test]
    fn test_bmc_coerce_bv_to_bool() {
        // Array expects Bool, value is BV32 → should convert via != 0.
        let arr_sort = Sort::array(ptr_sort(), bool_sort());
        let value = Expr::var("v32", Sort::bv32());
        let coerced =
            coerce_store_value_bmc(&arr_sort, &value, false).expect("should coerce BV32→Bool");
        assert!(coerced.sort().is_bool(), "coerced value should be Bool");
    }

    #[test]
    fn test_bmc_coerce_int_to_bv() {
        // Array expects BV64, value is Int → should convert via int2bv.
        let arr_sort = Sort::array(ptr_sort(), Sort::bitvec(64));
        let value = Expr::var("n", int_sort());
        let coerced =
            coerce_store_value_bmc(&arr_sort, &value, false).expect("should coerce Int→BV64");
        assert_eq!(coerced.sort().bitvec_width(), Some(64), "coerced value should be BV64");
    }

    #[test]
    fn test_bmc_coerce_bv_to_int_signedness() {
        // Part of #3055: BV→Int conversion respects signed parameter.
        let arr_sort = Sort::array(ptr_sort(), int_sort());
        let value = Expr::var("v32", Sort::bv32());
        // Unsigned: bare Bv2Int node (no ITE sign-extension).
        let unsigned = coerce_store_value_bmc(&arr_sort, &value, false).expect("unsigned BV→Int");
        assert!(unsigned.sort().is_int());
        assert!(!format!("{:?}", unsigned).contains("Ite"), "unsigned: no ITE, got {:?}", unsigned);
        // Signed: bv2int_signed expands to ITE(msb==1, bv2int-2^width, bv2int).
        let signed = coerce_store_value_bmc(&arr_sort, &value, true).expect("signed BV→Int");
        assert!(signed.sort().is_int());
        assert!(format!("{:?}", signed).contains("Ite"), "signed: expect ITE, got {:?}", signed);
    }

    #[test]
    fn test_bmc_coerce_matching_sorts_returns_none() {
        // Matching sorts → no coercion needed.
        let arr_sort = Sort::array(ptr_sort(), Sort::bv32());
        let value = Expr::var("v32", Sort::bv32());
        assert!(
            coerce_store_value_bmc(&arr_sort, &value, false).is_none(),
            "matching sorts should return None"
        );
    }

    #[test]
    fn test_bmc_coerce_datatype_to_bv_returns_none_for_complex() {
        // Complex datatype with non-BV fields → flattening may fail → returns None.
        let nested_dt = struct_sort("Inner", [("fld_a", int_sort()), ("fld_b", bool_sort())]);
        let dt = struct_sort("Outer", [("fld_inner", nested_dt)]);
        let arr_sort = Sort::array(ptr_sort(), Sort::bitvec(64));
        let value = Expr::var("outer_val", dt);
        // flatten_datatype_to_bitvec requires all-BV leaves; Int leaves → None.
        assert!(
            coerce_store_value_bmc(&arr_sort, &value, false).is_none(),
            "complex datatype with non-BV leaves should return None"
        );
    }

    #[test]
    fn test_bmc_fallback_name_unique() {
        let name1 = bmc_store_fallback_name();
        let name2 = bmc_store_fallback_name();
        assert_ne!(name1, name2, "fallback names should be unique");
        assert!(
            name1.starts_with("__bmc_store_coercion_"),
            "fallback name should have expected prefix"
        );
    }
}
