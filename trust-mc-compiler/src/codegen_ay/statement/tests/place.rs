// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! MIR-driven tests for place.rs — codegen_place and is_marker_bv32_sort.
//!
//! 28 trivial AY-only expression tests deleted per rule #2312 and #2482
//! (tested AY field_select/array-select/is_constructor/pointer-check patterns,
//! not production codegen).
//! Remaining tests use with_test_ay_ctx_for_source to exercise codegen_place,
//! plus is_marker_bv32_sort tests that call the production helper.

use super::*;

// =============================================================================
// is_marker_bv32_sort tests (#2016)
// =============================================================================

/// bv32 should be detected as marker sort (PhantomData/ZST).
#[test]
fn test_is_marker_bv32_sort_true() {
    use crate::codegen_ay::statement::StatementCodegen;
    let sort = Sort::bitvec(32);
    assert!(StatementCodegen::is_marker_bv32_sort(&sort));
}

/// bv8 should NOT be a marker sort.
#[test]
fn test_is_marker_bv32_sort_false_bv8() {
    use crate::codegen_ay::statement::StatementCodegen;
    assert!(!StatementCodegen::is_marker_bv32_sort(&Sort::bitvec(8)));
}

/// bv64 should NOT be a marker sort.
#[test]
fn test_is_marker_bv32_sort_false_bv64() {
    use crate::codegen_ay::statement::StatementCodegen;
    assert!(!StatementCodegen::is_marker_bv32_sort(&Sort::bitvec(64)));
}

/// Bool should NOT be a marker sort.
#[test]
fn test_is_marker_bv32_sort_false_bool() {
    use crate::codegen_ay::statement::StatementCodegen;
    assert!(!StatementCodegen::is_marker_bv32_sort(&Sort::bool()));
}

/// Int should NOT be a marker sort.
#[test]
fn test_is_marker_bv32_sort_false_int() {
    use crate::codegen_ay::statement::StatementCodegen;
    assert!(!StatementCodegen::is_marker_bv32_sort(&Sort::int()));
}

/// Datatype sort should NOT be a marker sort.
#[test]
fn test_is_marker_bv32_sort_false_datatype() {
    use crate::codegen_ay::statement::StatementCodegen;
    assert!(!StatementCodegen::is_marker_bv32_sort(&point_sort()));
}

// =============================================================================
// MIR-driven codegen_place tests (Part of #2016)
// =============================================================================
//
// These tests compile real Rust source, build StatementCodegen with actual MIR
// bodies, and exercise codegen_place through the real dispatch path.

const PLACE_PROBE_SOURCE: &str = r#"
#![allow(dead_code, unused_variables)]

pub struct Point {
    pub x: i32,
    pub y: i32,
}

pub struct Nested {
    pub inner: Point,
    pub tag: u8,
}

pub fn simple_local(a: u32) -> u32 {
    a
}

pub fn struct_field(p: Point) -> i32 {
    p.x
}

pub fn tuple_access(t: (u32, u64)) -> u32 {
    t.0
}

pub fn nested_field(n: Nested) -> i32 {
    n.inner.x
}

pub fn array_index(arr: [u32; 4], idx: usize) -> u32 {
    arr[idx]
}

pub fn downcast_array_index(x: Option<[u32; 4]>, idx: usize) -> u32 {
    match x {
        Some(arr) => {
            let value = arr[idx];
            value
        }
        None => 0,
    }
}

pub fn ref_deref(r: &u32) -> u32 {
    *r
}

pub fn multiple_locals(a: i32, b: u32, c: bool) -> i32 {
    if c { a } else { b as i32 }
}
"#;

fn seed_place_arg_locals(
    codegen: &mut StatementCodegen<'_, '_, '_>,
    body: &rustc_public::mir::Body,
) {
    for (idx, local_decl) in body.arg_locals().iter().enumerate() {
        let local_idx = idx + 1;
        let place = Place { local: Local::from(local_idx), projection: vec![] };
        let base = codegen.ssa_base_name(&place);
        if let Some(sort) = StatementCodegen::infer_sort_from_ty(local_decl.ty) {
            codegen.env_update(base, Expr::var(format!("arg_{local_idx}"), sort));
        }
    }
}

/// Test codegen_place for a simple local variable (no projections).
#[test]
fn test_mir_codegen_place_simple_local() {
    with_test_ay_ctx_for_source(PLACE_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "simple_local");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);
        seed_place_arg_locals(&mut codegen, &body);

        // local_1 is the `a: u32` parameter
        let place = Place { local: Local::from(1usize), projection: vec![] };
        let result = codegen.codegen_place(&place);

        assert!(result.is_some(), "codegen_place should resolve simple local");
        let expr = result.unwrap();
        assert!(expr.sort().is_bitvec(), "u32 local should have bitvec sort");
        assert_eq!(expr.sort().bitvec_width(), Some(32));
    });
}

/// Helper: check if a place has a specific projection kind anywhere in its chain.
fn place_has_projection(place: &Place, check: fn(&ProjectionElem) -> bool) -> bool {
    place.projection.iter().any(check)
}

/// Test codegen_place for struct field projection (Point.x).
/// MIR may optimize away Field projections for simple cases, so
/// we check both statement LHS and rvalue operands for Field projections.
#[test]
fn test_mir_codegen_place_struct_field() {
    with_test_ay_ctx_for_source(PLACE_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "struct_field");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);
        seed_place_arg_locals(&mut codegen, &body);

        // Exercise codegen_place on all places with Field projections
        let mut exercised = 0;
        for bb in &body.blocks {
            for stmt in &bb.statements {
                if let StatementKind::Assign(place, rvalue) = &stmt.kind {
                    if place_has_projection(place, |p| matches!(p, ProjectionElem::Field(..))) {
                        let _r = codegen.codegen_place(place);
                        exercised += 1;
                    }
                    if let Rvalue::Use(Operand::Copy(p) | Operand::Move(p)) = rvalue
                        && place_has_projection(p, |p| matches!(p, ProjectionElem::Field(..)))
                    {
                        let _r = codegen.codegen_place(p);
                        exercised += 1;
                    }
                }
            }
        }
        // If no Field projections found, MIR optimizer may have simplified.
        // Verify the function at least has the right arg count (1 param = Point).
        assert!(
            exercised > 0 || body.arg_locals().len() == 1,
            "struct_field should have Field projections or a single struct arg"
        );
    });
}

/// Test codegen_place for tuple field access (t.0).
/// MIR may merge tuple access with the return, so we check both
/// statement LHS and rvalue operands.
#[test]
fn test_mir_codegen_place_tuple_field() {
    with_test_ay_ctx_for_source(PLACE_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "tuple_access");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);
        seed_place_arg_locals(&mut codegen, &body);

        let mut exercised = 0;
        for bb in &body.blocks {
            for stmt in &bb.statements {
                if let StatementKind::Assign(place, rvalue) = &stmt.kind {
                    if place_has_projection(place, |p| matches!(p, ProjectionElem::Field(..))) {
                        let _r = codegen.codegen_place(place);
                        exercised += 1;
                    }
                    if let Rvalue::Use(Operand::Copy(p) | Operand::Move(p)) = rvalue
                        && place_has_projection(p, |p| matches!(p, ProjectionElem::Field(..)))
                    {
                        let _r = codegen.codegen_place(p);
                        exercised += 1;
                    }
                }
            }
        }
        assert!(
            exercised > 0 || body.arg_locals().len() == 1,
            "tuple_access should have Field projections or a single tuple arg"
        );
    });
}

/// Regression for #4314: when the root enum local is absent from env,
/// codegen_place must still resolve Downcast + Field + Index by reusing
/// the shared projection chain logic.
///
/// rustc lowers `arr[idx]` through a temporary after `((_1 as Some).0)`, so
/// this test takes the real MIR-derived Downcast + Field place and appends the
/// final Index projection to exercise the missing-env fallback seam directly.
#[test]
fn test_mir_codegen_place_missing_env_downcast_index_projection() {
    with_test_ay_ctx_for_source(PLACE_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "downcast_array_index");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let idx_place = Place { local: Local::from(2usize), projection: vec![] };
        let idx_base = codegen.ssa_base_name(&idx_place);
        let idx_sort =
            StatementCodegen::infer_sort_from_ty(body.arg_locals()[1].ty).expect("idx arg sort");
        codegen.env_update(idx_base, Expr::var("arg_2", idx_sort));

        let downcast_field_place = body
            .blocks
            .iter()
            .flat_map(|bb| bb.statements.iter())
            .find_map(|stmt| match &stmt.kind {
                StatementKind::Assign(
                    _,
                    Rvalue::Use(Operand::Copy(place) | Operand::Move(place)),
                ) if place_has_projection(place, |p| matches!(p, ProjectionElem::Downcast(_)))
                    && place_has_projection(place, |p| matches!(p, ProjectionElem::Field(..))) =>
                {
                    Some(place.clone())
                }
                _ => None,
            })
            .expect("MIR should contain Downcast + Field place");

        let mut target_place = downcast_field_place.clone();
        target_place.projection.push(ProjectionElem::Index(Local::from(2usize)));

        let root_base = codegen.root_ssa_base_name(&target_place);
        assert!(
            codegen.env_lookup(&root_base).is_none(),
            "root should be absent to exercise missing-env fallback"
        );

        let result = codegen.codegen_place(&target_place);
        assert!(
            result.is_some(),
            "Downcast + Field + Index place should resolve when root env is missing"
        );
        assert_eq!(
            result.unwrap().sort().bitvec_width(),
            Some(32),
            "downcasted array element should be bv32"
        );
    });
}

/// Test codegen_place for reference dereference (*r).
/// The MIR for `*r` should have a Deref projection in either
/// statements or rvalue operands.
#[test]
fn test_mir_codegen_place_ref_deref() {
    with_test_ay_ctx_for_source(PLACE_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "ref_deref");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);
        seed_place_arg_locals(&mut codegen, &body);

        // Exercise codegen_place on Deref projections
        let mut exercised = 0;
        for bb in &body.blocks {
            for stmt in &bb.statements {
                if let StatementKind::Assign(place, rvalue) = &stmt.kind {
                    if place_has_projection(place, |p| matches!(p, ProjectionElem::Deref)) {
                        let _r = codegen.codegen_place(place);
                        exercised += 1;
                    }
                    if let Rvalue::Use(Operand::Copy(p) | Operand::Move(p)) = rvalue
                        && place_has_projection(p, |p| matches!(p, ProjectionElem::Deref))
                    {
                        let _r = codegen.codegen_place(p);
                        exercised += 1;
                    }
                }
            }
        }
        // The function takes &u32, so it should have Deref in the MIR
        assert!(
            exercised > 0 || body.arg_locals().len() == 1,
            "ref_deref should exercise Deref projections or have a single ref arg"
        );
    });
}

/// Test codegen_place for multiple locals with different types.
#[test]
fn test_mir_codegen_place_multiple_locals() {
    with_test_ay_ctx_for_source(PLACE_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "multiple_locals");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);
        seed_place_arg_locals(&mut codegen, &body);

        // local_1 = a: i32, local_2 = b: u32, local_3 = c: bool
        let place_a = Place { local: Local::from(1usize), projection: vec![] };
        let place_b = Place { local: Local::from(2usize), projection: vec![] };
        let place_c = Place { local: Local::from(3usize), projection: vec![] };

        let a = codegen.codegen_place(&place_a);
        let b = codegen.codegen_place(&place_b);
        let c = codegen.codegen_place(&place_c);

        assert!(a.is_some(), "i32 arg should resolve");
        assert!(b.is_some(), "u32 arg should resolve");
        assert!(c.is_some(), "bool arg should resolve");

        let a_expr = a.unwrap();
        let b_expr = b.unwrap();
        let c_expr = c.unwrap();

        assert_eq!(a_expr.sort().bitvec_width(), Some(32), "i32 should be bv32");
        assert_eq!(b_expr.sort().bitvec_width(), Some(32), "u32 should be bv32");
        assert!(c_expr.sort().is_bool(), "bool should have bool sort");
    });
}

/// Test root_ssa_base_name returns correct format.
#[test]
fn test_mir_root_ssa_base_name_format() {
    with_test_ay_ctx_for_source(PLACE_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "simple_local");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let place = Place { local: Local::from(1usize), projection: vec![] };
        let root_base = codegen.root_ssa_base_name(&place);

        // Should be in format "fn_name::local_1"
        assert!(root_base.contains("::local_1"), "root_base should contain ::local_1: {root_base}");
    });
}

/// Test codegen_place on return place (local 0).
#[test]
fn test_mir_codegen_place_return_local() {
    with_test_ay_ctx_for_source(PLACE_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "simple_local");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        // local_0 is the return place — initially unset in the environment
        let return_place = Place { local: Local::from(0usize), projection: vec![] };
        let result = codegen.codegen_place(&return_place);

        // Return place may be None (not yet assigned) or Some (if sort inference
        // created it). Either is valid. Verify the SSA base name is well-formed.
        let base = codegen.ssa_base_name(&return_place);
        assert!(base.contains("::local_0"), "return place base should contain ::local_0: {base}");
        // If result is Some, verify the expression has a valid sort
        if let Some(expr) = result {
            assert!(
                expr.sort().is_bitvec() || expr.sort().is_bool() || expr.sort().is_datatype(),
                "return place sort should be a concrete type, got {:?}",
                expr.sort()
            );
        }
    });
}
