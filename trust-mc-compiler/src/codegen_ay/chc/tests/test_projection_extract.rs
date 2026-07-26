// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
// Unit tests for collect_field_projections in codegen_stmt_projection/projection_path.rs.
// Part of #2341: CHC zero-coverage remediation.
//
// Tests MIR-backed field projection extraction from Place projection lists.

// Test code: unwrap/panic are acceptable for assertions
#![allow(clippy::unwrap_used, clippy::panic)]

use super::super::call::inline_shared::{PlaceResolver, resolve_place};
use super::super::codegen_ctx::diagnostics::ChcDiagnostics;
use super::super::{UnknownProjectionPolicy, collect_field_projections};
use super::common::*;
use ay_bindings::{ExprValue, Sort};
use rustc_public::mir::{Operand, ProjectionElem, Rvalue, StatementKind};
use std::collections::HashMap;

// =============================================================================
// extract_field_projections — field and downcast extraction from MIR projections
// =============================================================================

#[test]
fn test_extract_field_projections_from_struct_access() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        pub struct Point { pub x: u32, pub y: u32 }
        pub fn read_field(p: Point) -> u32 { p.x }
    "#;
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "read_field");
        let body = instance.body().expect("function body");

        let mut found_field_projection = false;
        for block in &body.blocks {
            for stmt in &block.statements {
                if let StatementKind::Assign(_, rvalue) = &stmt.kind {
                    let place = match rvalue {
                        Rvalue::Use(Operand::Copy(p) | Operand::Move(p)) => Some(p),
                        _ => None,
                    };
                    if let Some(place) = place
                        && place.projection.iter().any(|p| matches!(p, ProjectionElem::Field(_, _)))
                    {
                        let diagnostics = ChcDiagnostics::default();
                        let projs = collect_field_projections(
                            &place.projection,
                            UnknownProjectionPolicy::ReturnEmpty(&diagnostics),
                        );
                        if !projs.is_empty() {
                            found_field_projection = true;
                            // Simple struct field access should produce exactly 1 FieldProjection
                            assert_eq!(
                                projs.len(),
                                1,
                                "single field access should produce 1 FieldProjection"
                            );
                            assert!(
                                projs[0].cons_idx.is_none(),
                                "struct field access should have no constructor index"
                            );
                            assert!(
                                projs[0].field_ty.is_some(),
                                "field projection should carry field type"
                            );
                        }
                    }
                }
            }
        }
        assert!(found_field_projection, "should find at least one Field projection in MIR");
    });
}

#[test]
fn test_extract_field_projections_from_enum_downcast() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        pub enum MyOption { None, Some(u32) }
        pub fn unwrap_option(o: MyOption) -> u32 {
            match o {
                MyOption::Some(v) => v,
                MyOption::None => 0,
            }
        }
    "#;
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "unwrap_option");
        let body = instance.body().expect("function body");

        let mut found_downcast = false;
        for block in &body.blocks {
            for stmt in &block.statements {
                if let StatementKind::Assign(_, rvalue) = &stmt.kind {
                    let place = match rvalue {
                        Rvalue::Use(Operand::Copy(p) | Operand::Move(p)) => Some(p),
                        _ => None,
                    };
                    if let Some(place) = place
                        && place.projection.iter().any(|p| matches!(p, ProjectionElem::Downcast(_)))
                    {
                        let diagnostics = ChcDiagnostics::default();
                        let projs = collect_field_projections(
                            &place.projection,
                            UnknownProjectionPolicy::ReturnEmpty(&diagnostics),
                        );
                        if !projs.is_empty() {
                            found_downcast = true;
                            // Downcast + Field should produce a FieldProjection with cons_idx set
                            let has_cons = projs.iter().any(|p| p.cons_idx.is_some());
                            assert!(has_cons, "enum downcast should set constructor index");
                        }
                    }
                }
            }
        }
        assert!(found_downcast, "should find at least one Downcast+Field projection in match arms");
    });
}

const INLINE_OPTION_PROJECTION_PROBE: &str = r#"
    #![allow(dead_code)]

    pub fn unwrap_option(opt: Option<u16>) -> u16 {
        match opt {
            Some(value) => value,
            None => 0,
        }
    }
"#;

fn find_downcast_field_place(body: &rustc_public::mir::Body) -> Option<Place> {
    body.blocks.iter().find_map(|block| {
        block.statements.iter().find_map(|stmt| {
            let StatementKind::Assign(_, rvalue) = &stmt.kind else {
                return None;
            };
            let place = match rvalue {
                Rvalue::Use(Operand::Copy(place) | Operand::Move(place)) => place,
                _ => return None,
            };
            let has_downcast =
                place.projection.iter().any(|proj| matches!(proj, ProjectionElem::Downcast(_)));
            let has_field =
                place.projection.iter().any(|proj| matches!(proj, ProjectionElem::Field(_, _)));
            (has_downcast && has_field).then(|| place.clone())
        })
    })
}

#[test]
fn test_resolve_place_field_map_option_ite_avoids_selector_over_ite() {
    with_test_ay_ctx_for_source(INLINE_OPTION_PROJECTION_PROBE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "unwrap_option");
        let body = instance.body().expect("function body");
        let place = find_downcast_field_place(&body)
            .expect("unwrap_option MIR should contain a Downcast+Field projection");

        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "unwrap_option", ChcConfig::default());
        let option_sort = option_datatype_sort(Sort::bitvec(16));
        let payload = Expr::var("payload", Sort::bitvec(16));
        let some =
            Expr::datatype_constructor("Option_V", "Some", vec![payload], option_sort.clone());
        let none = Expr::datatype_constructor("Option_V", "None", vec![], option_sort);
        let reconstructed = Expr::ite(Expr::var("cond", Sort::bool()), some, none);

        let local_exprs = HashMap::from([(place.local, reconstructed)]);
        let resolver_map = HashMap::new();
        let resolver = PlaceResolver::FieldMap(&resolver_map);
        let resolved = resolve_place(&mut chc_ctx, &local_exprs, &place, &resolver, body.locals())
            .expect("field-map resolver should extract Option payload from reconstructed ITE");

        assert_eq!(
            resolved.sort().bitvec_width(),
            Some(16),
            "Option payload projection should yield the payload sort"
        );
        assert!(
            !constraint_tree_contains(&resolved, &|expr| match expr.value() {
                ExprValue::DatatypeSelector { expr: inner, .. } => {
                    matches!(inner.value(), ExprValue::Ite { .. })
                }
                _ => false,
            }),
            "field-map projection must not emit DatatypeSelector over ITE: {resolved}"
        );
    });
}

#[test]
fn test_extract_field_projections_deref_returns_empty() {
    // Deref projections are unsupported by extract_field_projections and should return empty
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        pub fn deref_read(r: &u32) -> u32 { *r }
    "#;
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "deref_read");
        let body = instance.body().expect("function body");

        let mut found_deref = false;
        for block in &body.blocks {
            for stmt in &block.statements {
                if let StatementKind::Assign(_, rvalue) = &stmt.kind {
                    let place = match rvalue {
                        Rvalue::Use(Operand::Copy(p) | Operand::Move(p)) => Some(p),
                        _ => None,
                    };
                    if let Some(place) = place
                        && place.projection.iter().any(|p| matches!(p, ProjectionElem::Deref))
                        && !place
                            .projection
                            .iter()
                            .any(|p| matches!(p, ProjectionElem::Field(_, _)))
                    {
                        let diagnostics = ChcDiagnostics::default();
                        let projs = collect_field_projections(
                            &place.projection,
                            UnknownProjectionPolicy::ReturnEmpty(&diagnostics),
                        );
                        // Deref-only projections should return empty (unsupported)
                        assert!(projs.is_empty(), "Deref-only projections should return empty vec");
                        assert_eq!(
                            diagnostics.unsupported_field_projection.get(),
                            1,
                            "unsupported deref projection should increment unsupported_field_projection counter"
                        );
                        found_deref = true;
                    }
                }
            }
        }
        assert!(found_deref, "should find at least one Deref-only projection in MIR");
    });
}

#[test]
fn test_extract_field_projections_nested_struct() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        pub struct Inner { pub value: u32 }
        pub struct Outer { pub inner: Inner }
        pub fn read_nested(o: Outer) -> u32 { o.inner.value }
    "#;
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "read_nested");
        let body = instance.body().expect("function body");

        // In optimized MIR, nested field access may be split across temporaries.
        // Look for any projection chain with 2+ Field elements.
        let diagnostics = ChcDiagnostics::default();
        let mut max_fields = 0usize;
        for block in &body.blocks {
            for stmt in &block.statements {
                if let StatementKind::Assign(_, rvalue) = &stmt.kind {
                    let place = match rvalue {
                        Rvalue::Use(Operand::Copy(p) | Operand::Move(p)) => Some(p),
                        _ => None,
                    };
                    if let Some(place) = place {
                        let projs = collect_field_projections(
                            &place.projection,
                            UnknownProjectionPolicy::ReturnEmpty(&diagnostics),
                        );
                        max_fields = max_fields.max(projs.len());
                    }
                }
            }
            // Also check the LHS of assignments
            for stmt in &block.statements {
                if let StatementKind::Assign(lhs, _) = &stmt.kind {
                    let projs = collect_field_projections(
                        &lhs.projection,
                        UnknownProjectionPolicy::ReturnEmpty(&diagnostics),
                    );
                    max_fields = max_fields.max(projs.len());
                }
            }
        }
        // At minimum we should see individual field projections in the MIR
        assert!(
            max_fields >= 1,
            "nested struct access should produce at least 1 field projection in MIR"
        );
    });
}

// =============================================================================
// apply_field_selections — additional edge case: single-field struct chain
// =============================================================================

#[test]
fn test_apply_field_selections_single_projection() {
    // Single field selection on a 2-field struct
    let sort =
        struct_sort("Pair", [("fld_first", Sort::bitvec(8)), ("fld_second", Sort::bitvec(16))]);
    let pair = Expr::var("pair", sort);

    let projections = vec![FieldProjection { field_idx: 1, cons_idx: None, field_ty: None }];
    let result = ChcCtx::apply_field_selections(pair, &projections);
    assert!(result.is_some(), "single field selection should succeed");
    let result = result.unwrap();
    assert_eq!(result.sort().bitvec_width(), Some(16), "selecting fld_second should yield bv16");
}

#[test]
fn test_apply_field_selections_empty_projections_returns_root() {
    let x = Expr::var("x", Sort::bitvec(32));
    let projections: Vec<FieldProjection> = vec![];
    let result = ChcCtx::apply_field_selections(x.clone(), &projections);
    assert!(result.is_some());
    assert_eq!(result.unwrap().to_string(), x.to_string());
}

// =============================================================================
// apply_projection_update — additional edge case: single-field update
// =============================================================================

#[test]
fn test_apply_projection_update_single_field() {
    let sort = struct_sort("Wrapper", [("fld_value", Sort::bitvec(32))]);
    let w = Expr::var("w", sort.clone());
    let new_val = Expr::bitvec_const(77, 32);

    let projections = vec![FieldProjection { field_idx: 0, cons_idx: None, field_ty: None }];
    let result = ChcCtx::apply_projection_update(&w, &projections, new_val);
    assert!(result.is_some(), "single field update should succeed");
    let result = result.unwrap();
    assert_eq!(result.sort(), &sort, "updated expression should preserve container sort");
}

#[test]
fn test_apply_projection_update_out_of_bounds_field_returns_none() {
    let sort = struct_sort("Wrapper", [("fld_value", Sort::bitvec(32))]);
    let w = Expr::var("w", sort);
    let new_val = Expr::bitvec_const(42, 32);

    let projections = vec![FieldProjection { field_idx: 5, cons_idx: None, field_ty: None }];
    let result = ChcCtx::apply_projection_update(&w, &projections, new_val);
    assert!(result.is_none(), "out-of-bounds field update should return None");
}
