// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

use super::common::*;
use ay_bindings::Expr;
use rustc_public::mir::{
    AggregateKind, BinOp, CastKind, Operand, PointerCoercion, ProjectionElem, Rvalue, StatementKind,
};
use rustc_public::ty::{RigidTy, TyKind};

const SEEDED_DISCRIMINANT: u64 = 11;
const SEEDED_PROMOTED_OBJ_ID: u32 = 77;
const SEEDED_REF_TARGET_LOCAL: usize = 999;

const COPY_CAST_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub fn probe_copy_cast(src: *const u8) -> *const u8 {
        let casted = src as *mut u8;
        let copied = casted as *const u8;
        let shadow = copied;
        shadow
    }
"#;

const OFFSET_SOURCE: &str = r#"
    #![allow(dead_code)]
    #![allow(internal_features)]
    #![feature(core_intrinsics)]

    use std::intrinsics::offset;

    pub unsafe fn probe_offset(base: *const u8) -> *const u8 {
        let stepped = unsafe { offset(base, 2_isize) };
        let shadow = stepped;
        shadow
    }
"#;

const AGGREGATE_FIELD_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub fn probe_aggregate_field(src: *const u8) -> *const u8 {
        let pair = (src, 1u8);
        let projected = pair.0;
        projected
    }
"#;

const OPTION_PAYLOAD_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub fn probe_option_payload(s: &str) -> &str {
        match Some(s) {
            Some(projected) => projected,
            None => s,
        }
    }
"#;

const REF_SUBSLICE_SOURCE: &str = r#"
    #![allow(dead_code)]

    // Force an explicit Rvalue::Ref in MIR. Taking a shared borrow of
    // a mutable reference's target produces an Rvalue::Ref that the
    // MIR optimizer retains (unlike &*shared which is elided).
    pub fn probe_ref_subslice(src: &mut [u8]) -> &[u8] {
        &*src
    }
"#;

const ADDRESS_OF_SUBSLICE_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub fn probe_addressof_subslice(src: &mut [u8]) -> *const [u8] {
        &raw const *src
    }
"#;

fn seeded_len_expr() -> Expr {
    Expr::bitvec_const(5u64, crate::codegen_ay::types::POINTER_WIDTH)
}

fn seeded_offset_expr() -> Expr {
    Expr::bitvec_const(1u64, crate::codegen_ay::types::POINTER_WIDTH)
}

fn seeded_value_expr() -> Expr {
    Expr::bitvec_const(7u64, 8)
}

fn seeded_slice_view_expr() -> Expr {
    Expr::bool_const(true)
}

fn seed_ref_metadata(
    chc_ctx: &mut ChcCtx<'_, '_>,
    src_local: usize,
    mark_forwarded: bool,
) -> (Expr, Expr, Expr) {
    let value_expr = seeded_value_expr();
    let len_expr = seeded_len_expr();
    let offset_expr = seeded_offset_expr();

    chc_ctx
        .ref_resolution
        .ref_targets
        .insert(src_local, RefTarget::with_projections(SEEDED_REF_TARGET_LOCAL, vec![]));
    if mark_forwarded {
        chc_ctx.ref_resolution.call_forwarded_raw_ptrs.insert(src_local);
    }
    chc_ctx.ref_resolution.const_ref_values.insert(src_local, value_expr.clone());
    chc_ctx.ref_resolution.const_ref_discriminants.insert(src_local, SEEDED_DISCRIMINANT);
    chc_ctx.ref_resolution.const_ref_promoted_obj_ids.insert(src_local, SEEDED_PROMOTED_OBJ_ID);
    chc_ctx.ref_resolution.subslice_len.insert(src_local, len_expr.clone());
    chc_ctx.ref_resolution.subslice_offset.insert(src_local, offset_expr.clone());

    (value_expr, len_expr, offset_expr)
}

fn assert_seeded_metadata(
    chc_ctx: &ChcCtx<'_, '_>,
    local: usize,
    expected_value: &Expr,
    expected_len: &Expr,
    expected_offset: &Expr,
    expect_forwarded: bool,
) {
    let ref_target =
        chc_ctx.ref_resolution.ref_targets.get(&local).expect("expected propagated ref_target");
    assert_eq!(
        ref_target.local, SEEDED_REF_TARGET_LOCAL,
        "local {local} should keep the seeded referent local"
    );
    assert!(
        ref_target.projections.is_empty(),
        "local {local} should keep the seeded ref_target projections"
    );

    let value = chc_ctx
        .ref_resolution
        .const_ref_values
        .get(&local)
        .expect("expected propagated const_ref_values")
        .to_string();
    assert_eq!(value, expected_value.to_string(), "local {local} should preserve const_ref_values");

    let len = chc_ctx
        .ref_resolution
        .subslice_len
        .get(&local)
        .expect("expected propagated subslice_len")
        .to_string();
    assert_eq!(len, expected_len.to_string(), "local {local} should preserve subslice_len");

    let offset = chc_ctx
        .ref_resolution
        .subslice_offset
        .get(&local)
        .expect("expected propagated subslice_offset")
        .to_string();
    assert_eq!(
        offset,
        expected_offset.to_string(),
        "local {local} should preserve subslice_offset"
    );

    assert_eq!(
        chc_ctx.ref_resolution.const_ref_discriminants.get(&local).copied(),
        Some(SEEDED_DISCRIMINANT),
        "local {local} should preserve const_ref_discriminants"
    );
    assert_eq!(
        chc_ctx.ref_resolution.const_ref_promoted_obj_ids.get(&local).copied(),
        Some(SEEDED_PROMOTED_OBJ_ID),
        "local {local} should preserve const_ref_promoted_obj_ids"
    );
    assert_eq!(
        chc_ctx.ref_resolution.call_forwarded_raw_ptrs.contains(&local),
        expect_forwarded,
        "unexpected call_forwarded_raw_ptrs state for local {local}"
    );
}

fn find_copy_cast_dests(body: &rustc_public::mir::Body) -> (usize, usize, usize, usize) {
    let arg_count = body.arg_locals().len();
    let mut raw_ptr_edges = Vec::new();

    for (bb_idx, block) in body.blocks.iter().enumerate() {
        for stmt in &block.statements {
            let StatementKind::Assign(lhs, rhs) = &stmt.kind else {
                continue;
            };
            if !lhs.projection.is_empty() || (lhs.local != 0 && lhs.local <= arg_count) {
                continue;
            }
            if !matches!(body.locals()[lhs.local].ty.kind(), TyKind::RigidTy(RigidTy::RawPtr(_, _)))
            {
                continue;
            }
            match rhs {
                Rvalue::Use(Operand::Copy(src) | Operand::Move(src))
                | Rvalue::Cast(_, Operand::Copy(src) | Operand::Move(src), _)
                    if src.projection.is_empty() =>
                {
                    raw_ptr_edges.push((bb_idx, src.local, lhs.local));
                }
                _ => {}
            }
        }
    }

    let (bb_idx, arg_local, first_dest) = raw_ptr_edges
        .iter()
        .copied()
        .find(|(_, src_local, _)| *src_local == arg_count)
        .expect("expected first raw-pointer copy/cast edge from function argument");
    let (_, _, second_dest) = raw_ptr_edges
        .iter()
        .copied()
        .find(|(edge_bb_idx, src_local, _)| *edge_bb_idx == bb_idx && *src_local == first_dest)
        .expect("expected second raw-pointer copy/cast edge from first temp");

    (bb_idx, arg_local, first_dest, second_dest)
}

fn find_aggregate_field_dest(body: &rustc_public::mir::Body) -> (usize, usize, usize) {
    let arg_local = body.arg_locals().len();
    let aggregate_local = body
        .blocks
        .iter()
        .flat_map(|block| block.statements.iter())
        .find_map(|stmt| {
            let StatementKind::Assign(lhs, Rvalue::Aggregate(AggregateKind::Tuple, operands)) =
                &stmt.kind
            else {
                return None;
            };
            let Some(Operand::Copy(src) | Operand::Move(src)) = operands.first() else {
                return None;
            };
            if lhs.projection.is_empty() && src.projection.is_empty() && src.local == arg_local {
                Some(lhs.local)
            } else {
                None
            }
        })
        .expect("expected tuple aggregate carrying the pointer argument");

    let (bb_idx, projected_local) = body
        .blocks
        .iter()
        .enumerate()
        .find_map(|(bb_idx, block)| {
            block.statements.iter().find_map(|stmt| {
                let StatementKind::Assign(
                    lhs,
                    Rvalue::Use(Operand::Copy(place) | Operand::Move(place)),
                ) = &stmt.kind
                else {
                    return None;
                };
                if lhs.projection.is_empty()
                    && place.local == aggregate_local
                    && place.projection.len() == 1
                    && matches!(place.projection[0], ProjectionElem::Field(0, _))
                {
                    Some((bb_idx, lhs.local))
                } else {
                    None
                }
            })
        })
        .expect("expected aggregate field projection assignment");

    (bb_idx, arg_local, projected_local)
}

fn find_option_payload_dest(body: &rustc_public::mir::Body) -> (usize, usize, usize) {
    body.blocks
        .iter()
        .enumerate()
        .find_map(|(bb_idx, block)| {
            block.statements.iter().find_map(|stmt| {
                let StatementKind::Assign(
                    lhs,
                    Rvalue::Use(Operand::Copy(place) | Operand::Move(place)),
                ) = &stmt.kind
                else {
                    return None;
                };
                if lhs.projection.is_empty()
                    && place
                        .projection
                        .last()
                        .is_some_and(|proj| matches!(proj, ProjectionElem::Field(0, _)))
                    && place
                        .projection
                        .iter()
                        .any(|proj| matches!(proj, ProjectionElem::Downcast(_)))
                {
                    Some((bb_idx, place.local, lhs.local))
                } else {
                    None
                }
            })
        })
        .expect("expected Downcast(Some)+Field(0) payload projection assignment")
}

fn find_ref_rvalue_dest(body: &rustc_public::mir::Body) -> (usize, usize, usize) {
    body.blocks
        .iter()
        .enumerate()
        .find_map(|(bb_idx, block)| {
            block.statements.iter().find_map(|stmt| {
                let StatementKind::Assign(lhs, Rvalue::Ref(_, _, place)) = &stmt.kind else {
                    return None;
                };
                if lhs.projection.is_empty() {
                    Some((bb_idx, place.local, lhs.local))
                } else {
                    None
                }
            })
        })
        .expect("expected Rvalue::Ref assignment")
}

fn find_addressof_rvalue_dest(body: &rustc_public::mir::Body) -> (usize, usize, usize) {
    body.blocks
        .iter()
        .enumerate()
        .find_map(|(bb_idx, block)| {
            block.statements.iter().find_map(|stmt| {
                let StatementKind::Assign(lhs, Rvalue::AddressOf(_, place)) = &stmt.kind else {
                    return None;
                };
                if lhs.projection.is_empty() {
                    Some((bb_idx, place.local, lhs.local))
                } else {
                    None
                }
            })
        })
        .expect("expected Rvalue::AddressOf assignment")
}

#[test]
fn test_encode_block_statements_aggregate_field_source_propagates_full_ref_metadata() {
    with_test_ay_ctx_for_source(AGGREGATE_FIELD_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_aggregate_field");
        let body = instance.body().expect("function body");
        let mut chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "probe_aggregate_field", ChcConfig::default());
        let (bb_idx, src_local, projected_local) = find_aggregate_field_dest(&body);
        let (value_expr, len_expr, offset_expr) = seed_ref_metadata(&mut chc_ctx, src_local, false);

        let _ = chc_ctx.encode_block_statements(bb_idx);

        assert_seeded_metadata(
            &chc_ctx,
            projected_local,
            &value_expr,
            &len_expr,
            &offset_expr,
            false,
        );
    });
}

#[test]
fn test_encode_block_statements_option_payload_projection_propagates_slice_metadata() {
    with_test_ay_ctx_for_source(OPTION_PAYLOAD_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_option_payload");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_option_payload", ChcConfig::default());
        let (bb_idx, option_local, projected_local) = find_option_payload_dest(&body);
        let (value_expr, len_expr, offset_expr) =
            seed_ref_metadata(&mut chc_ctx, option_local, false);
        let slice_view_expr = seeded_slice_view_expr();
        chc_ctx.ref_resolution.const_ref_slice_views.insert(option_local, slice_view_expr.clone());

        let _ = chc_ctx.encode_block_statements(bb_idx);

        assert_seeded_metadata(
            &chc_ctx,
            projected_local,
            &value_expr,
            &len_expr,
            &offset_expr,
            false,
        );
        let propagated_slice_view = chc_ctx
            .ref_resolution
            .const_ref_slice_views
            .get(&projected_local)
            .expect("expected propagated const_ref_slice_views");
        assert_eq!(
            propagated_slice_view.to_string(),
            slice_view_expr.to_string(),
            "option payload projection should preserve const_ref_slice_views"
        );
    });
}

#[test]
fn test_encode_block_statements_copy_cast_propagates_full_ref_metadata() {
    with_test_ay_ctx_for_source(COPY_CAST_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_copy_cast");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_copy_cast", ChcConfig::default());
        let (bb_idx, src_local, cast_dest_local, final_local) = find_copy_cast_dests(&body);
        let (value_expr, len_expr, offset_expr) = seed_ref_metadata(&mut chc_ctx, src_local, false);

        let _ = chc_ctx.encode_block_statements(bb_idx);

        assert_seeded_metadata(
            &chc_ctx,
            cast_dest_local,
            &value_expr,
            &len_expr,
            &offset_expr,
            true,
        );
        assert_seeded_metadata(&chc_ctx, final_local, &value_expr, &len_expr, &offset_expr, true);
    });
}

#[test]
fn test_encode_block_statements_call_forwarded_copy_cast_keeps_subslice_len() {
    with_test_ay_ctx_for_source(COPY_CAST_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_copy_cast");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_copy_cast", ChcConfig::default());
        let (bb_idx, src_local, cast_dest_local, final_local) = find_copy_cast_dests(&body);
        let (value_expr, len_expr, offset_expr) = seed_ref_metadata(&mut chc_ctx, src_local, true);

        let _ = chc_ctx.encode_block_statements(bb_idx);

        assert_seeded_metadata(
            &chc_ctx,
            cast_dest_local,
            &value_expr,
            &len_expr,
            &offset_expr,
            true,
        );
        assert_seeded_metadata(&chc_ctx, final_local, &value_expr, &len_expr, &offset_expr, true);
    });
}

#[test]
fn test_encode_block_statements_offset_propagates_const_side_tables() {
    with_test_ay_ctx_for_source(OFFSET_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_offset");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_offset", ChcConfig::default());

        let (bb_idx, base_local, stepped_local) = body
            .blocks
            .iter()
            .enumerate()
            .find_map(|(bb_idx, block)| {
                block.statements.iter().find_map(|stmt| {
                    let StatementKind::Assign(lhs, rhs) = &stmt.kind else {
                        return None;
                    };
                    match rhs {
                        Rvalue::BinaryOp(BinOp::Offset, base_op, _)
                        | Rvalue::CheckedBinaryOp(BinOp::Offset, base_op, _) => {
                            let (Operand::Copy(base_place) | Operand::Move(base_place)) = base_op
                            else {
                                return None;
                            };
                            if lhs.projection.is_empty() && base_place.projection.is_empty() {
                                Some((bb_idx, base_place.local, lhs.local))
                            } else {
                                None
                            }
                        }
                        _ => None,
                    }
                })
            })
            .expect("expected MIR BinOp::Offset assignment");

        let (value_expr, len_expr, base_offset_expr) =
            seed_ref_metadata(&mut chc_ctx, base_local, false);
        let expected_offset = base_offset_expr
            .bvadd(Expr::bitvec_const(2u64, crate::codegen_ay::types::POINTER_WIDTH));

        let _ = chc_ctx.encode_block_statements(bb_idx);

        assert_seeded_metadata(
            &chc_ctx,
            stepped_local,
            &value_expr,
            &len_expr,
            &expected_offset,
            true,
        );
    });
}

// ---------- Part of #4163: custom-DST Unsize metadata propagation ----------

const CUSTOM_DST_UNSIZE_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub struct Wrapper<T: ?Sized> {
        header: u8,
        data: T,
    }

    pub fn probe_custom_dst_unsize(w: &Wrapper<[u8; 3]>) -> &Wrapper<[u8]> {
        w
    }
"#;

/// Find the `PointerCoercion::Unsize` cast edge in the MIR for the custom-DST
/// probe. Returns `(bb_idx, src_local, dest_local)`.
fn find_custom_dst_unsize_edge(body: &rustc_public::mir::Body) -> (usize, usize, usize) {
    for (bb_idx, block) in body.blocks.iter().enumerate() {
        for stmt in &block.statements {
            let StatementKind::Assign(lhs, rhs) = &stmt.kind else {
                continue;
            };
            if let Rvalue::Cast(CastKind::PointerCoercion(PointerCoercion::Unsize), operand, _) =
                rhs
            {
                let src_local = match operand {
                    Operand::Copy(place) | Operand::Move(place) if place.projection.is_empty() => {
                        place.local
                    }
                    _ => continue,
                };
                if lhs.projection.is_empty() {
                    return (bb_idx, src_local, lhs.local);
                }
            }
        }
    }
    panic!("expected PointerCoercion::Unsize cast in probe_custom_dst_unsize MIR");
}

/// Part of #4163 D3: verify that `encode_block_statements` propagates
/// `subslice_len` through a `PointerCoercion::Unsize` cast targeting a
/// custom DST (ADT with slice tail).
#[test]
fn test_encode_block_statements_custom_dst_unsize_propagates_subslice_len() {
    with_test_ay_ctx_for_source(CUSTOM_DST_UNSIZE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_custom_dst_unsize");
        let body = instance.body().expect("function body");
        let mut chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "probe_custom_dst_unsize", ChcConfig::default());
        let (bb_idx, src_local, dest_local) = find_custom_dst_unsize_edge(&body);

        // Seed subslice_len on the source (simulates upstream metadata tracking).
        let len_expr = seeded_len_expr();
        chc_ctx.ref_resolution.subslice_len.insert(src_local, len_expr.clone());

        let _ = chc_ctx.encode_block_statements(bb_idx);

        // D3 assertion: subslice_len must propagate to the Unsize destination.
        let propagated = chc_ctx
            .ref_resolution
            .subslice_len
            .get(&dest_local)
            .expect("expected subslice_len propagated to custom-DST Unsize destination");
        assert_eq!(
            propagated.to_string(),
            len_expr.to_string(),
            "custom-DST Unsize cast should preserve subslice_len from source to destination"
        );
    });
}

/// Part of #4163 D2: verify that `unsize_metadata_lost` is NOT recorded when
/// the Unsize target is a custom DST (ADT with slice tail). Before #4163, all
/// non-array-to-slice Unsize casts were classified as metadata lost.
#[test]
fn test_custom_dst_unsize_does_not_record_metadata_lost() {
    let _guard = crate::codegen_ay::test_fixtures::METADATA_COUNTER_MUTEX
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    let _ = crate::codegen_ay::take_translation_drop_site_reasons_by_fn();

    with_test_ay_ctx_for_source(CUSTOM_DST_UNSIZE_SOURCE, |ctx| {
        let fn_name = "probe_custom_dst_unsize";
        let instance = find_instance_by_suffix(ctx.tcx, fn_name);
        let body = instance.body().expect("function body");
        let _vc = mir_to_chc(ctx.tcx, &body, fn_name, ChcConfig::default());

        let reasons = crate::codegen_ay::take_translation_drop_site_reasons_by_fn();
        let fn_reasons = reasons.get(fn_name);
        let has_metadata_lost =
            fn_reasons.map(|r| r.contains_key("unsize_metadata_lost")).unwrap_or(false);
        assert!(
            !has_metadata_lost,
            "custom-DST Unsize cast should NOT record unsize_metadata_lost; got: {fn_reasons:?}"
        );
    });
}

/// Part of #4178 D4: explicit `Rvalue::Ref` regression for `subslice_len`
/// propagation on current HEAD.
#[test]
fn test_encode_block_statements_ref_propagates_subslice_len() {
    with_test_ay_ctx_for_source(REF_SUBSLICE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_ref_subslice");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_ref_subslice", ChcConfig::default());
        let (bb_idx, src_local, dest_local) = find_ref_rvalue_dest(&body);

        let len_expr = seeded_len_expr();
        chc_ctx.ref_resolution.subslice_len.insert(src_local, len_expr.clone());

        let _ = chc_ctx.encode_block_statements(bb_idx);

        let propagated = chc_ctx
            .ref_resolution
            .subslice_len
            .get(&dest_local)
            .expect("expected subslice_len propagated through Rvalue::Ref");
        assert_eq!(
            propagated.to_string(),
            len_expr.to_string(),
            "Rvalue::Ref should preserve subslice_len from source to destination"
        );
    });
}

/// Part of #4178 D4: explicit `Rvalue::AddressOf` regression for `subslice_len`
/// propagation on current HEAD.
#[test]
fn test_encode_block_statements_addressof_propagates_subslice_len() {
    with_test_ay_ctx_for_source(ADDRESS_OF_SUBSLICE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_addressof_subslice");
        let body = instance.body().expect("function body");
        let mut chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "probe_addressof_subslice", ChcConfig::default());
        let (bb_idx, src_local, dest_local) = find_addressof_rvalue_dest(&body);

        let len_expr = seeded_len_expr();
        chc_ctx.ref_resolution.subslice_len.insert(src_local, len_expr.clone());

        let _ = chc_ctx.encode_block_statements(bb_idx);

        let propagated = chc_ctx
            .ref_resolution
            .subslice_len
            .get(&dest_local)
            .expect("expected subslice_len propagated through Rvalue::AddressOf");
        assert_eq!(
            propagated.to_string(),
            len_expr.to_string(),
            "Rvalue::AddressOf should preserve subslice_len from source to destination"
        );
    });
}
