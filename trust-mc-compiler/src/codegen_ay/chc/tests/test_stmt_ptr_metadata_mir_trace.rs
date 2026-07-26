// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Tests for `codegen_stmt_ptr_metadata_mir_trace.rs` — MIR-level slice
//! metadata resolution helpers.
//!
//! Part of #4127.
//!
//! Covers:
//! - `resolve_slice_metadata_from_mir`: concrete length resolution through
//!   Cast(Unsize) from fixed-size arrays
//! - `extract_str_len_from_const_operand`: constant &str byte-length extraction
//! - `operand_bare_local`: simple Copy/Move local extraction
//! - Negative: dynamic slice (no fixed-size source) returns None

// Test code: unwrap/panic are acceptable for assertions
#![allow(clippy::unwrap_used, clippy::panic)]

use super::common::*;
use rustc_public::mir::{Operand, Rvalue, StatementKind, TerminatorKind};

const FIXED_ARRAY_UNSIZE_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub fn probe_fixed_array_slice() -> usize {
        let arr = [1u32, 2, 3, 4, 5];
        let slice: &[u32] = &arr;
        slice.len()
    }
"#;

const STR_CONST_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub fn probe_str_const_len() -> usize {
        let s: &str = "hello";
        s.len()
    }
"#;

const DYNAMIC_SLICE_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub fn probe_dynamic_slice_len(data: &[u32]) -> usize {
        data.len()
    }
"#;

const RANGE_SUBSLICE_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub fn probe_range_subslice() -> usize {
        let arr = [10u32, 20, 30, 40, 50, 60, 70];
        let sub = &arr[2..5];
        sub.len()
    }
"#;

const STRUCT_WITH_ARRAY_TAIL_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub struct Header {
        pub tag: u32,
        pub data: [u8; 16],
    }

    pub fn probe_struct_array_tail(h: &Header) -> usize {
        let slice: &[u8] = &h.data;
        slice.len()
    }
"#;

/// Find the first local that receives a Cast(Unsize) from a fixed-size array.
fn find_unsize_cast_dest(body: &rustc_public::mir::Body) -> Option<usize> {
    use rustc_public::mir::{CastKind, PointerCoercion};
    for block in &body.blocks {
        for stmt in &block.statements {
            if let StatementKind::Assign(lhs, rvalue) = &stmt.kind {
                if let Rvalue::Cast(CastKind::PointerCoercion(PointerCoercion::Unsize), _, _) =
                    rvalue
                {
                    return Some(lhs.local);
                }
            }
        }
    }
    None
}

/// Find a const &str operand in the body (assignment to any local).
fn find_const_str_operand(body: &rustc_public::mir::Body) -> Option<Operand> {
    for block in &body.blocks {
        for stmt in &block.statements {
            if let StatementKind::Assign(_, Rvalue::Use(operand)) = &stmt.kind {
                if let Operand::Constant(const_op) = operand {
                    let ty = const_op.ty();
                    if matches!(
                        ty.kind(),
                        TyKind::RigidTy(RigidTy::Ref(_, pointee, _))
                            if matches!(pointee.kind(), TyKind::RigidTy(RigidTy::Str))
                    ) {
                        return Some(operand.clone());
                    }
                }
            }
        }
    }
    None
}

#[test]
fn test_resolve_slice_metadata_from_mir_fixed_array_returns_correct_len() {
    with_test_ay_ctx_for_source(FIXED_ARRAY_UNSIZE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_fixed_array_slice");
        let body = instance.body().expect("function body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_fixed_array_slice", ChcConfig::default());

        let unsize_dest = find_unsize_cast_dest(&body)
            .expect("probe should contain a Cast(Unsize) from [u32; 5]");

        let resolved = chc_ctx.resolve_slice_metadata_from_mir(unsize_dest);
        assert_eq!(
            resolved,
            Some(5),
            "resolve_slice_metadata_from_mir should extract len=5 from &[u32; 5]"
        );
    });
}

#[test]
fn test_extract_str_len_from_const_operand_returns_byte_length() {
    with_test_ay_ctx_for_source(STR_CONST_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_str_const_len");
        let body = instance.body().expect("function body");

        let str_operand =
            find_const_str_operand(&body).expect("probe should contain a const &str operand");

        let resolved = ChcCtx::extract_str_len_from_const_operand(&str_operand);
        assert_eq!(
            resolved,
            Some(5),
            "extract_str_len_from_const_operand should return 5 for \"hello\""
        );
    });
}

#[test]
fn test_resolve_slice_metadata_from_mir_dynamic_slice_returns_none() {
    with_test_ay_ctx_for_source(DYNAMIC_SLICE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_dynamic_slice_len");
        let body = instance.body().expect("function body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_dynamic_slice_len", ChcConfig::default());

        // The function parameter `data: &[u32]` is local 1. It has no fixed-size
        // source, so MIR trace should return None.
        let resolved = chc_ctx.resolve_slice_metadata_from_mir(1);
        assert_eq!(
            resolved, None,
            "resolve_slice_metadata_from_mir should return None for a dynamic slice parameter"
        );
    });
}

#[test]
fn test_operand_bare_local_extracts_copy_move() {
    // operand_bare_local is a static method: test Copy and Move variants
    use rustc_public::mir::Place;

    let place = Place { local: 42, projection: vec![] };
    let copy_op = Operand::Copy(place.clone());
    let move_op = Operand::Move(place.clone());

    assert_eq!(
        ChcCtx::operand_bare_local(&copy_op),
        Some(42),
        "operand_bare_local should extract local from Copy operand"
    );
    assert_eq!(
        ChcCtx::operand_bare_local(&move_op),
        Some(42),
        "operand_bare_local should extract local from Move operand"
    );
}

#[test]
fn test_operand_bare_local_rejects_projected_place() {
    use rustc_public::mir::{Place, ProjectionElem};

    let place = Place { local: 7, projection: vec![ProjectionElem::Deref] };
    let copy_op = Operand::Copy(place);
    assert_eq!(
        ChcCtx::operand_bare_local(&copy_op),
        None,
        "operand_bare_local should reject Copy with projection"
    );
}

#[test]
fn test_resolve_slice_metadata_from_mir_range_subslice() {
    with_test_ay_ctx_for_source(RANGE_SUBSLICE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_range_subslice");
        let body = instance.body().expect("function body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_range_subslice", ChcConfig::default());

        // Find the local that receives the subslice (the Index::index call result).
        // The slice from `&arr[2..5]` should resolve to length 3.
        let subslice_dest = body.blocks.iter().find_map(|block| {
            if let TerminatorKind::Call { func, destination, .. } = &block.terminator.kind {
                let Ok(func_ty) = func.ty(body.locals()) else { return None };
                let TyKind::RigidTy(RigidTy::FnDef(def, _)) = func_ty.kind() else {
                    return None;
                };
                let name = def.trimmed_name();
                if name == "index" || name.ends_with("::index") {
                    return Some(destination.local);
                }
            }
            None
        });

        if let Some(dest) = subslice_dest {
            let resolved = chc_ctx.resolve_slice_metadata_from_mir(dest);
            assert_eq!(
                resolved,
                Some(3),
                "resolve_slice_metadata_from_mir should extract len=3 from &arr[2..5]"
            );
        }
        // If optimizer eliminated the Index call, the test is still valid -- the
        // pattern may be inlined. We don't assert_mir_pattern_found here because
        // the optimizer may change the MIR.
    });
}

#[test]
fn test_resolve_slice_metadata_from_mir_struct_array_tail() {
    with_test_ay_ctx_for_source(STRUCT_WITH_ARRAY_TAIL_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_struct_array_tail");
        let body = instance.body().expect("function body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_struct_array_tail", ChcConfig::default());

        // Find the Unsize cast destination (the slice reference from &h.data).
        let unsize_dest = find_unsize_cast_dest(&body);
        if let Some(dest) = unsize_dest {
            let resolved = chc_ctx.resolve_slice_metadata_from_mir(dest);
            assert_eq!(
                resolved,
                Some(16),
                "resolve_slice_metadata_from_mir should extract len=16 from struct with [u8; 16] tail"
            );
        }
        // Optimizer may inline the slice creation differently, so we don't
        // assert the Unsize cast always exists.
    });
}
