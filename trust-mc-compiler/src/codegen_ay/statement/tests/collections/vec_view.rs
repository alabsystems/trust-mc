// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Tests for collections/vec_view.rs: Vec view, pointer, and iterator stubs.
//!
//! Covers codegen_vec_view_stub paths for:
//! - VecIntoIter with real operand → produces VecIntoIter datatype
//! - VecIter with real ref operand → produces VecIter datatype
//! - VecIterMut with real ref operand → produces VecIterMut datatype
//! - VecAsSlice with real ref operand → produces Slice datatype
//! - VecIter with Slice ref operand → produces iterator wrapping Slice (#3602)
//!
//! The warn (empty args) paths for these stubs are already covered
//! in vec_mir.rs. These tests exercise the success paths.
//!
//! Part of #2303: zero-coverage production file test coverage.

use super::*;
use std::sync::Arc;

fn assigned_expr_for_place(
    codegen: &mut StatementCodegen<'_, '_, '_>,
    place: &Place,
) -> Option<Expr> {
    let base = codegen.ssa_base_name(place);
    codegen.env_lookup(&base).cloned()
}

fn make_test_vec(len: u64, cap: u64) -> Expr {
    let elem_sort = Sort::bitvec(32);
    let array_sort = Sort::array(Sort::bitvec(POINTER_WIDTH), elem_sort);
    let vec_sort_name = "Vec_bv32";
    let vec_sort = struct_sort(
        vec_sort_name,
        [
            ("fld_ptr", Sort::bitvec(POINTER_WIDTH)),
            ("fld_len", Sort::bitvec(POINTER_WIDTH)),
            ("fld_cap", Sort::bitvec(POINTER_WIDTH)),
            ("fld_data", array_sort),
        ],
    );
    let ptr = Expr::bitvec_const(0x1000u64, POINTER_WIDTH);
    let len_expr = Expr::bitvec_const(len, POINTER_WIDTH);
    let cap_expr = Expr::bitvec_const(cap, POINTER_WIDTH);
    let default_elem = Expr::bitvec_const(0u64, 32);
    let data = Expr::const_array(Sort::bitvec(POINTER_WIDTH), default_elem);
    let ctor_name = vec_sort
        .datatype_default_constructor()
        .map_or_else(|| crate::codegen_ay::names::cons_name(vec_sort_name), str::to_string);
    Expr::datatype_constructor(
        vec_sort_name,
        ctor_name,
        vec![ptr, len_expr, cap_expr, data],
        vec_sort,
    )
}

/// Test VecIntoIter with real Vec operand produces iterator datatype.
/// vec_view.rs: VecIntoIter branch — creates VecIntoIter with (fld_vec, fld_pos).
#[test]
fn test_codegen_vec_view_into_iter_real_operand_produces_datatype() {
    use crate::codegen_ay::stubs::StubKind;
    with_test_ay_ctx_for_source(COLLECTIONS_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe_u32");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let vec_op = seed_collections_local(&mut codegen, 1, make_test_vec(3, 10));
        let dest = Place { local: 0, projection: vec![] };
        let result = codegen.codegen_vec_stub(
            StubKind::VecIntoIter,
            &[vec_op],
            &dest,
            Some(1),
            "<Vec<u32> as IntoIterator>::into_iter",
        );
        assert_eq!(result, Some(1));

        let dest_expr = assigned_expr_for_place(&mut codegen, &dest)
            .expect("VecIntoIter should assign destination");
        assert!(
            dest_expr.sort().is_datatype(),
            "VecIntoIter should produce datatype sort, got {:?}",
            dest_expr.sort()
        );
        let dt_name = dest_expr.sort().datatype_name().unwrap_or("");
        assert!(
            dt_name.starts_with("VecIntoIter"),
            "VecIntoIter sort name should start with 'VecIntoIter', got '{}'",
            dt_name
        );
    });
}

/// Test VecIter with ref-resolved Vec produces iterator datatype.
/// vec_view.rs: VecIter branch — creates VecIter with (fld_vec, fld_pos).
#[test]
fn test_codegen_vec_view_iter_ref_resolved_produces_datatype() {
    use crate::codegen_ay::stubs::StubKind;
    with_test_ay_ctx_for_source(COLLECTIONS_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe_u32");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        // VecIter takes &self — seed a Vec and set up ref_pointees so
        // get_map_base_from_ref can resolve the reference.
        let vec_val = make_test_vec(5, 10);
        let fn_name =
            codegen.ctx.current_fn().map_or_else(|| "unknown".to_string(), |f| f.name.clone());
        let vec_base = format!("{}::local_2", fn_name);
        codegen.env_update(vec_base.clone(), vec_val);

        // Seed local_1 as a reference pointing to local_2
        let ref_base = format!("{}::local_1", fn_name);
        let ref_expr = Expr::bitvec_const(0x2000u64, POINTER_WIDTH);
        codegen.env_update(ref_base.clone(), ref_expr);
        codegen.ref_pointees.insert(Arc::from(ref_base), Arc::from(vec_base));

        let ref_op = Operand::Copy(Place { local: 1, projection: vec![] });
        let dest = Place { local: 0, projection: vec![] };
        let result = codegen.codegen_vec_stub(
            StubKind::VecIter,
            &[ref_op],
            &dest,
            Some(2),
            "alloc::vec::Vec::iter",
        );
        assert_eq!(result, Some(2));

        let dest_expr = assigned_expr_for_place(&mut codegen, &dest)
            .expect("VecIter should assign destination when ref resolves");
        assert!(
            dest_expr.sort().is_datatype(),
            "VecIter should produce datatype sort, got {:?}",
            dest_expr.sort()
        );
    });
}

/// Test VecIterMut with ref-resolved Vec produces iterator datatype.
/// vec_view.rs: VecIterMut branch — creates VecIterMut with (fld_vec, fld_pos).
#[test]
fn test_codegen_vec_view_iter_mut_ref_resolved_produces_datatype() {
    use crate::codegen_ay::stubs::StubKind;
    with_test_ay_ctx_for_source(COLLECTIONS_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe_u32");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let vec_val = make_test_vec(2, 8);
        let fn_name =
            codegen.ctx.current_fn().map_or_else(|| "unknown".to_string(), |f| f.name.clone());
        let vec_base = format!("{}::local_2", fn_name);
        codegen.env_update(vec_base.clone(), vec_val);

        let ref_base = format!("{}::local_1", fn_name);
        let ref_expr = Expr::bitvec_const(0x3000u64, POINTER_WIDTH);
        codegen.env_update(ref_base.clone(), ref_expr);
        codegen.ref_pointees.insert(Arc::from(ref_base), Arc::from(vec_base));

        let ref_op = Operand::Copy(Place { local: 1, projection: vec![] });
        let dest = Place { local: 0, projection: vec![] };
        let result = codegen.codegen_vec_stub(
            StubKind::VecIterMut,
            &[ref_op],
            &dest,
            Some(3),
            "alloc::vec::Vec::iter_mut",
        );
        assert_eq!(result, Some(3));

        let dest_expr = assigned_expr_for_place(&mut codegen, &dest)
            .expect("VecIterMut should assign destination when ref resolves");
        assert!(
            dest_expr.sort().is_datatype(),
            "VecIterMut should produce datatype sort, got {:?}",
            dest_expr.sort()
        );
    });
}

/// Test VecAsSlice with ref-resolved Vec produces Slice datatype.
/// vec_view.rs: VecAsSlice branch — creates Slice with (fld_ptr, fld_len, fld_data).
#[test]
fn test_codegen_vec_view_as_slice_ref_resolved_produces_slice() {
    use crate::codegen_ay::stubs::StubKind;
    with_test_ay_ctx_for_source(COLLECTIONS_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe_u32");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let vec_val = make_test_vec(4, 8);
        let fn_name =
            codegen.ctx.current_fn().map_or_else(|| "unknown".to_string(), |f| f.name.clone());
        let vec_base = format!("{}::local_2", fn_name);
        codegen.env_update(vec_base.clone(), vec_val);

        let ref_base = format!("{}::local_1", fn_name);
        let ref_expr = Expr::bitvec_const(0x4000u64, POINTER_WIDTH);
        codegen.env_update(ref_base.clone(), ref_expr);
        codegen.ref_pointees.insert(Arc::from(ref_base), Arc::from(vec_base));

        let ref_op = Operand::Copy(Place { local: 1, projection: vec![] });
        let dest = Place { local: 0, projection: vec![] };
        let result = codegen.codegen_vec_stub(
            StubKind::VecAsSlice,
            &[ref_op],
            &dest,
            Some(4),
            "alloc::vec::Vec::as_slice",
        );
        assert_eq!(result, Some(4));

        let dest_expr = assigned_expr_for_place(&mut codegen, &dest)
            .expect("VecAsSlice should assign destination when ref resolves");
        assert!(
            dest_expr.sort().is_datatype(),
            "VecAsSlice should produce datatype (Slice) sort, got {:?}",
            dest_expr.sort()
        );
        let dt_name = dest_expr.sort().datatype_name().unwrap_or("");
        assert_eq!(dt_name, "Slice_bv32", "VecAsSlice should produce typed Slice sort");
    });
}

/// Test VecIntoIter with empty args hits warn path (no assignment).
/// vec_view.rs: VecIntoIter branch — guard for empty args.
#[test]
fn test_codegen_vec_view_into_iter_empty_args_warn_path() {
    use crate::codegen_ay::stubs::StubKind;
    with_test_ay_ctx_for_source(COLLECTIONS_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe_u32");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let dest = Place { local: 0, projection: vec![] };
        let result = codegen.codegen_vec_stub(
            StubKind::VecIntoIter,
            &[],
            &dest,
            Some(5),
            "<Vec<u32> as IntoIterator>::into_iter",
        );
        assert_eq!(result, Some(5));
        assert!(
            assigned_expr_for_place(&mut codegen, &dest).is_none(),
            "VecIntoIter warn path should not assign destination"
        );
    });
}

/// Test VecIter and VecIterMut with empty args hit warn path.
/// vec_view.rs: VecIter/VecIterMut branches — guard for empty args.
#[test]
fn test_codegen_vec_view_iter_empty_args_warn_path() {
    use crate::codegen_ay::stubs::StubKind;
    for (stub_kind, callee_path) in [
        (StubKind::VecIter, "alloc::vec::Vec::iter"),
        (StubKind::VecIterMut, "alloc::vec::Vec::iter_mut"),
    ] {
        with_test_ay_ctx_for_source(COLLECTIONS_PROBE_SOURCE, |mut ctx| {
            let instance = find_instance_by_suffix(&ctx, "probe_u32");
            let body = instance.body().expect("function body");
            ctx.set_current_fn(instance);
            let tuple_usage = TupleUsageAnalysis::run(&body);
            let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

            let dest = Place { local: 0, projection: vec![] };
            let result = codegen.codegen_vec_stub(stub_kind, &[], &dest, Some(6), callee_path);
            assert_eq!(result, Some(6));
            assert!(
                assigned_expr_for_place(&mut codegen, &dest).is_none(),
                "{:?} warn path should not assign destination",
                stub_kind
            );
        });
    }
}

fn make_test_slice(len: u64) -> Expr {
    let elem_sort = Sort::bitvec(32);
    let array_sort = Sort::array(Sort::bitvec(POINTER_WIDTH), elem_sort);
    let slice_sort_name = "Slice_bv32";
    let slice_sort = struct_sort(
        slice_sort_name,
        [
            ("fld_ptr", Sort::bitvec(POINTER_WIDTH)),
            ("fld_len", Sort::bitvec(POINTER_WIDTH)),
            ("fld_data", array_sort),
        ],
    );
    let ptr = Expr::bitvec_const(0x5000u64, POINTER_WIDTH);
    let len_expr = Expr::bitvec_const(len, POINTER_WIDTH);
    let default_elem = Expr::bitvec_const(0u64, 32);
    let data = Expr::const_array(Sort::bitvec(POINTER_WIDTH), default_elem);
    let ctor_name = slice_sort
        .datatype_default_constructor()
        .map_or_else(|| crate::codegen_ay::names::cons_name(slice_sort_name), str::to_string);
    Expr::datatype_constructor(slice_sort_name, ctor_name, vec![ptr, len_expr, data], slice_sort)
}

/// Test VecIter with slice-backed ref produces iterator wrapping Slice.
/// Part of #3602: slice IntoIterator reuses VecIter — BMC parity guard.
/// Seeds a Slice_bv32 behind a reference, routes through VecIter, and verifies
/// the iterator construction succeeds with a datatype result whose fld_vec
/// carries the Slice sort.
#[test]
fn test_codegen_vec_view_iter_slice_ref_produces_slice_backed_iterator() {
    use crate::codegen_ay::stubs::StubKind;
    with_test_ay_ctx_for_source(COLLECTIONS_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe_u32");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        // Seed a Slice_bv32 value at local_2, reference it from local_1.
        let slice_val = make_test_slice(4);
        let fn_name =
            codegen.ctx.current_fn().map_or_else(|| "unknown".to_string(), |f| f.name.clone());
        let slice_base = format!("{}::local_2", fn_name);
        codegen.env_update(slice_base.clone(), slice_val);

        let ref_base = format!("{}::local_1", fn_name);
        let ref_expr = Expr::bitvec_const(0x6000u64, POINTER_WIDTH);
        codegen.env_update(ref_base.clone(), ref_expr);
        codegen.ref_pointees.insert(Arc::from(ref_base), Arc::from(slice_base));

        let ref_op = Operand::Copy(Place { local: 1, projection: vec![] });
        let dest = Place { local: 0, projection: vec![] };
        let result = codegen.codegen_vec_stub(
            StubKind::VecIter,
            &[ref_op],
            &dest,
            Some(7),
            "core::slice::iter::<impl IntoIterator for &[u32]>::into_iter",
        );
        assert_eq!(result, Some(7));

        let dest_expr = assigned_expr_for_place(&mut codegen, &dest)
            .expect("VecIter on Slice ref should assign destination");
        assert!(
            dest_expr.sort().is_datatype(),
            "VecIter on Slice should produce datatype sort, got {:?}",
            dest_expr.sort()
        );
        let dt_name = dest_expr.sort().datatype_name().unwrap_or("");
        assert!(
            dt_name.contains("Slice"),
            "Iterator sort name should reference Slice, got '{}'",
            dt_name
        );
    });
}
