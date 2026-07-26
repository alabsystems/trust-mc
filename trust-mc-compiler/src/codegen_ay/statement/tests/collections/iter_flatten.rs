// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Tests for collections/iter_flatten.rs: iterator flatten and collect operations.
//!
//! Covers:
//! - `codegen_iter_collect_vec`: Collect VecIntoIter back to Vec
//! - `codegen_iter_flatten_from_vec_iter`: Flatten nested Vec<Vec<T>> iterator
//! - `make_vec_from_parts`: Construct Vec from (elem_sort, len, data) — also in iter.rs
//! - `make_vec_into_iter`: Wrap Vec in VecIntoIter — also in iter.rs
//! - `make_flatten_iter`: Wrap iterator in Flatten — also in iter.rs
//!
//! The skip (non-datatype) paths are tested in iter.rs. These tests exercise
//! the success paths with real datatype iterators.
//!
//! Part of #2303: zero-coverage production file test coverage.

use super::*;
use crate::codegen_ay::names::{self, struct_sort};

fn with_iter_codegen<F>(callback: F)
where
    F: FnOnce(&mut StatementCodegen<'_, '_, '_>) + Send,
{
    with_test_ay_ctx_for_source(COLLECTIONS_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe_u32");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);
        callback(&mut codegen);
    });
}

/// Construct a Vec_bv32 expression for testing.
fn make_test_vec_bv32(codegen: &mut StatementCodegen<'_, '_, '_>, len: u64) -> Expr {
    let elem_sort = Sort::bitvec(32);
    let data_sort = Sort::array(Sort::bitvec(POINTER_WIDTH), elem_sort.clone());
    let data_name = codegen.ctx.fresh_name("test_data");
    let data = codegen.ctx.declare_var(&data_name, data_sort);
    let len_expr = Expr::bitvec_const(len, POINTER_WIDTH);
    codegen.make_vec_from_parts(elem_sort, len_expr, data)
}

// =============================================================================
// codegen_iter_collect_vec — success path tests
// =============================================================================

/// Test codegen_iter_collect_vec with a VecIntoIter at pos=0 returns the inner Vec.
/// iter_flatten.rs: codegen_iter_collect_vec — pos == 0 branch returns original vec.
#[test]
fn test_codegen_iter_collect_vec_from_vec_into_iter() {
    with_iter_codegen(|codegen| {
        let vec = make_test_vec_bv32(codegen, 3);
        let iter = codegen.make_vec_into_iter(vec);

        let result = codegen.codegen_iter_collect_vec(&iter);
        assert!(result.is_some(), "codegen_iter_collect_vec should succeed for VecIntoIter");

        let collected = result.unwrap();
        // Result should be a Vec datatype (ite of original vec vs symbolic)
        assert!(
            collected.sort().is_datatype(),
            "collected vec should be datatype, got {:?}",
            collected.sort()
        );
        let dt_name = collected.sort().datatype_name().unwrap_or("");
        assert!(
            dt_name.starts_with("Vec_"),
            "collected vec sort should start with 'Vec_', got '{}'",
            dt_name
        );
    });
}

/// Test codegen_iter_collect_vec with a Flatten wrapper over VecIntoIter.
/// iter_flatten.rs: codegen_iter_collect_vec — fld_iter extraction path.
#[test]
fn test_codegen_iter_collect_vec_from_flatten_wrapper() {
    with_iter_codegen(|codegen| {
        let vec = make_test_vec_bv32(codegen, 2);
        let iter = codegen.make_vec_into_iter(vec);
        let flatten = codegen.make_flatten_iter(iter);

        let result = codegen.codegen_iter_collect_vec(&flatten);
        assert!(result.is_some(), "codegen_iter_collect_vec should succeed for Flatten wrapper");

        let collected = result.unwrap();
        assert!(
            collected.sort().is_datatype(),
            "collected vec from flatten should be datatype, got {:?}",
            collected.sort()
        );
        let dt_name = collected.sort().datatype_name().unwrap_or("");
        assert!(
            dt_name.starts_with("Vec_"),
            "collected vec from flatten sort should start with 'Vec_', got '{}'",
            dt_name
        );
    });
}

// =============================================================================
// codegen_iter_flatten_from_vec_iter — success path tests
// =============================================================================

/// Test codegen_iter_flatten_from_vec_iter with a VecIntoIter of Vec<Vec<bv32>>.
/// iter_flatten.rs: codegen_iter_flatten_from_vec_iter — main logic path.
#[test]
fn test_codegen_iter_flatten_from_vec_of_vecs() {
    with_iter_codegen(|codegen| {
        // Build a Vec<Vec<bv32>> as outer container
        let inner_vec_0 = make_test_vec_bv32(codegen, 2);
        let inner_vec_1 = make_test_vec_bv32(codegen, 3);

        // Outer Vec: Array<usize, Vec_bv32> with len=2
        let outer_data_sort = Sort::array(Sort::bitvec(POINTER_WIDTH), inner_vec_0.sort().clone());
        let outer_data_name = codegen.ctx.fresh_name("outer_data");
        let outer_data_var = codegen.ctx.declare_var(&outer_data_name, outer_data_sort);
        // Store inner vecs at indices 0 and 1
        let idx0 = Expr::bitvec_const(0u64, POINTER_WIDTH);
        let idx1 = Expr::bitvec_const(1u64, POINTER_WIDTH);
        let stored_0 = outer_data_var.store(idx0, inner_vec_0.clone());
        let stored_1 = stored_0.store(idx1, inner_vec_1);

        // Build outer Vec from parts
        let outer_vec_sort_name = format!("Vec_{}", names::sort_short_name(inner_vec_0.sort()));
        let outer_len = Expr::bitvec_const(2u64, POINTER_WIDTH);
        let outer_vec_sort =
            struct_sort(outer_vec_sort_name.clone(), names::vec_fields(stored_1.sort().clone()));
        let ptr = Expr::bitvec_const(0x5000u64, POINTER_WIDTH);
        let ctor_name = outer_vec_sort.datatype_default_constructor().map_or_else(
            || crate::codegen_ay::names::cons_name(&outer_vec_sort_name),
            str::to_string,
        );
        let outer_vec = Expr::datatype_constructor(
            &outer_vec_sort_name,
            ctor_name,
            vec![ptr, outer_len.clone(), outer_len, stored_1],
            outer_vec_sort,
        );

        // Create VecIntoIter over the outer Vec
        let outer_iter = codegen.make_vec_into_iter(outer_vec);

        let result = codegen.codegen_iter_flatten_from_vec_iter(&outer_iter);
        assert!(
            result.is_some(),
            "codegen_iter_flatten_from_vec_iter should succeed for Vec<Vec<bv32>>"
        );

        let flattened = result.unwrap();
        assert!(
            flattened.sort().is_datatype(),
            "flattened iterator should be datatype sort, got {:?}",
            flattened.sort()
        );
        let dt_name = flattened.sort().datatype_name().unwrap_or("");
        assert!(
            dt_name.starts_with("Flatten_"),
            "flattened iterator sort should start with 'Flatten_', got '{}'",
            dt_name
        );
    });
}

// =============================================================================
// make_vec_from_parts — additional edge case
// =============================================================================

/// Test make_vec_from_parts with Int element sort (BigInt scenario).
/// iter_flatten.rs: make_vec_from_parts — sort name generation for non-bitvec.
#[test]
fn test_make_vec_from_parts_int_sort() {
    with_iter_codegen(|codegen| {
        let data_sort = Sort::array(Sort::bitvec(POINTER_WIDTH), Sort::int());
        let data_name = codegen.ctx.fresh_name("int_data");
        let data = codegen.ctx.declare_var(&data_name, data_sort);
        let len = Expr::bitvec_const(5u64, POINTER_WIDTH);

        let vec = codegen.make_vec_from_parts(Sort::int(), len, data);
        assert!(vec.sort().is_datatype());

        let dt_name = vec.sort().datatype_name().unwrap_or("");
        assert!(
            dt_name.starts_with("Vec_"),
            "make_vec_from_parts with Int sort should produce Vec_ prefixed name, got '{}'",
            dt_name
        );
    });
}
