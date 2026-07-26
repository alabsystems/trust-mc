// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Shared test fixtures for codegen_ay tests.
//!
//! This module provides common Sort and Expr constructors used across
//! multiple test files to reduce duplication and ensure consistency.
//!
//! See #1144 for rationale.

use crate::codegen_ay::names::{enum_sort, struct_sort};
use crate::codegen_ay::types::ptr_sort;
use ay_bindings::{Expr, Sort};
use rustc_middle::ty::TyCtxt;
use rustc_public::CrateDef;

/// Serializes tests that read or drain global metadata counters.
///
/// `generate_metadata()` consumes global `take_*` counters; tests that assert
/// exact counter values must hold this lock to avoid cross-test races.
pub(crate) static METADATA_COUNTER_MUTEX: std::sync::Mutex<()> = std::sync::Mutex::new(());

/// Creates a Point struct sort with x and y bitvec32 fields.
///
/// Fields use simple names ("x", "y") matching statement/tests convention.
/// Note: ay_bindings has an identical copy behind `#[cfg(test)]`, inaccessible
/// to downstream crates, so we keep a local version.
pub(crate) fn point_sort() -> Sort {
    struct_sort("Point", vec![("x", Sort::bitvec(32)), ("y", Sort::bitvec(32))])
}

/// Shared helper: find a function Instance by name suffix in the current crate.
///
/// Takes TyCtxt directly — callers with AYCtx can pass `ctx.tcx`.
/// Consolidates 2 identical copies (chc/tests/common.rs and statement/tests/mod.rs).
#[allow(clippy::panic)]
pub(crate) fn find_instance_by_suffix(
    tcx: TyCtxt<'_>,
    suffix: &str,
) -> rustc_public::mir::mono::Instance {
    let matches: Vec<_> = rustc_public::all_local_items()
        .into_iter()
        .filter(|item| {
            let def_id = rustc_public::rustc_internal::internal(tcx, item.def_id());
            let path = tcx.def_path_str(def_id);
            path == suffix || path.ends_with(&format!("::{suffix}"))
        })
        .collect();
    match matches.as_slice() {
        [] => panic!("missing item with suffix '{suffix}'"),
        [single] => {
            rustc_public::mir::mono::Instance::try_from(*single).expect("instance for item")
        }
        many => {
            let names: Vec<_> = many
                .iter()
                .map(|item| {
                    let def_id = rustc_public::rustc_internal::internal(tcx, item.def_id());
                    tcx.def_path_str(def_id)
                })
                .collect();
            panic!("ambiguous suffix '{suffix}': {} matches: {names:?}", many.len());
        }
    }
}

/// Creates a Point struct sort with prefixed field names ("fld_x", "fld_y").
///
/// Fields use prefixed names matching chc/tests.rs convention.
#[cfg(feature = "compiler-corpus-tests")]
pub(crate) fn point_sort_prefixed() -> Sort {
    struct_sort("Point", vec![("fld_x", Sort::bitvec(32)), ("fld_y", Sort::bitvec(32))])
}

/// Creates a Point expression with given x and y values.
#[cfg(feature = "compiler-corpus-tests")]
pub(crate) fn point_expr(x: u128, y: u128, sort: Sort) -> Expr {
    let x_val = Expr::bitvec_const(x, 32);
    let y_val = Expr::bitvec_const(y, 32);
    Expr::datatype_constructor("Point", "Point_mk", vec![x_val, y_val], sort)
}

/// Creates an Option-like struct sort with is_some (bool) and value fields.
///
/// This represents the struct encoding used by Rust's Option<T> in MIR.
#[cfg(feature = "compiler-corpus-tests")]
pub(crate) fn option_like_struct_sort(value_sort: Sort) -> Sort {
    struct_sort("Option", vec![("is_some", Sort::bool()), ("value", value_sort)])
}

// =========================================================================
// Iterator-related fixtures (Part of #1828)
// =========================================================================

/// Creates an Option<V> datatype sort with proper Some/None constructors.
///
/// This uses ay's datatype encoding for Rust's Option<T>:
/// - None: no fields
/// - Some: single "value" field
#[cfg(feature = "compiler-corpus-tests")]
pub(crate) fn option_datatype_sort(value_sort: Sort) -> Sort {
    enum_sort("Option_V", vec![("None", vec![]), ("Some", vec![("value", value_sort)])])
}

/// Creates a Result<T, E> datatype sort with proper Ok/Err constructors.
///
/// This uses ay's datatype encoding for Rust's Result<T, E>:
/// - Ok: single "value" field of type T
/// - Err: single "value" field of type E
pub(crate) fn result_datatype_sort(ok_sort: Sort, err_sort: Sort) -> Sort {
    enum_sort(
        "Result_T_E",
        vec![("Ok", vec![("value", ok_sort)]), ("Err", vec![("value", err_sort)])],
    )
}

/// Creates a HashMapIntoIter sort for testing iterator field extraction.
///
/// DT-free encoding (Part of #3057):
/// Structure: (data: Array<K, V>, present: Array<K, Bool>, keys: Array<usize, K>, pos: usize, len: usize)
#[cfg(feature = "compiler-corpus-tests")]
pub(crate) fn hashmap_iter_sort(key_sort: Sort, value_sort: Sort) -> Sort {
    let data_sort = Sort::array(key_sort.clone(), value_sort);
    let present_sort = Sort::array(key_sort.clone(), Sort::bool());
    let keys_sort = Sort::array(Sort::bitvec(64), key_sort);
    let pos_sort = Sort::bitvec(64);
    let len_sort = Sort::bitvec(64);

    struct_sort(
        "HashMapIntoIter",
        vec![
            ("fld_data", data_sort),
            ("fld_present", present_sort),
            ("fld_keys", keys_sort),
            ("fld_pos", pos_sort),
            ("fld_len", len_sort),
        ],
    )
}

/// Creates a HashSetIntoIter sort for testing iterator field extraction.
///
/// Structure: (set: Array<K, Bool>, keys: Array<usize, K>, pos: usize, len: usize)
#[cfg(feature = "compiler-corpus-tests")]
pub(crate) fn hashset_iter_sort(key_sort: Sort) -> Sort {
    let set_sort = Sort::array(key_sort.clone(), Sort::bool());
    let keys_sort = Sort::array(Sort::bitvec(64), key_sort);
    let pos_sort = Sort::bitvec(64);
    let len_sort = Sort::bitvec(64);

    struct_sort(
        "HashSetIntoIter",
        vec![
            ("fld_set", set_sort),
            ("fld_keys", keys_sort),
            ("fld_pos", pos_sort),
            ("fld_len", len_sort),
        ],
    )
}

/// Creates a Tuple<K, V> sort for testing tuple construction.
#[cfg(feature = "compiler-corpus-tests")]
pub(crate) fn tuple_sort(key_sort: Sort, value_sort: Sort) -> Sort {
    struct_sort("Tuple_K_V", vec![("fld_0", key_sort), ("fld_1", value_sort)])
}

// =========================================================================
// Entry-related fixtures (Part of #1830)
// =========================================================================

/// Creates a VacantEntry struct sort for BTreeMap/HashMap entry API.
///
/// VacantEntry contains pointer fields for key and map references.
#[cfg(feature = "compiler-corpus-tests")]
pub(crate) fn vacant_entry_sort() -> Sort {
    struct_sort("VacantEntry", vec![("fld_key", Sort::bitvec(64)), ("fld_map", Sort::bitvec(64))])
}

/// Creates an OccupiedEntry struct sort for BTreeMap/HashMap entry API.
///
/// OccupiedEntry contains pointer fields for key and map references.
#[cfg(feature = "compiler-corpus-tests")]
pub(crate) fn occupied_entry_sort() -> Sort {
    struct_sort("OccupiedEntry", vec![("fld_key", Sort::bitvec(64)), ("fld_map", Sort::bitvec(64))])
}

/// Creates an Entry enum sort with Vacant and Occupied variants.
///
/// Entry<K, V> is modeled as an enum where each variant wraps the
/// corresponding entry type (VacantEntry or OccupiedEntry).
/// This matches MIR's expectation for downcast projection access.
#[cfg(feature = "compiler-corpus-tests")]
pub(crate) fn entry_sort() -> Sort {
    enum_sort(
        "Entry",
        vec![
            ("Vacant", vec![("Vacant_field_0", vacant_entry_sort())]),
            ("Occupied", vec![("Occupied_field_0", occupied_entry_sort())]),
        ],
    )
}

// =========================================================================
// Collection fixtures (Part of #1871)
// =========================================================================

/// Creates a Vec<T> struct sort with ptr, len, cap, and data fields.
///
/// Vec is encoded as:
/// - fld_ptr: bitvec64 (pointer to backing storage)
/// - fld_len: bitvec64 (number of elements)
/// - fld_cap: bitvec64 (capacity)
/// - fld_data: Array<usize, T> (element storage)
pub(crate) fn vec_sort(elem_sort: Sort) -> Sort {
    let array_sort = Sort::array(ptr_sort(), elem_sort);
    struct_sort(
        "Vec",
        vec![
            ("fld_ptr", ptr_sort()),
            ("fld_len", ptr_sort()),
            ("fld_cap", ptr_sort()),
            ("fld_data", array_sort),
        ],
    )
}

/// Creates a Vec expression with given ptr, len, cap, and data.
pub(crate) fn vec_expr(ptr: Expr, len: Expr, cap: Expr, data: Expr, sort: Sort) -> Expr {
    let dt_name = sort.datatype_name().unwrap_or("Vec").to_owned();
    let cons_name = crate::codegen_ay::names::cons_name(&dt_name);
    Expr::datatype_constructor(&dt_name, cons_name, vec![ptr, len, cap, data], sort)
}
