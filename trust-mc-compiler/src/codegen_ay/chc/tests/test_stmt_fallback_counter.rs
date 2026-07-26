// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

// Test code: unwrap/panic are acceptable for assertions
#![allow(clippy::unwrap_used, clippy::panic)]

use super::common::*;
use ay_bindings::{Expr, Sort};
use rustc_public::mir::{Operand, ProjectionElem, Rvalue, StatementKind};

use rustc_public::mir::NonDivergingIntrinsic;

const SOURCE_COPY_ASSIGN: &str = r#"
    #![allow(dead_code, unused_assignments, unused_variables)]

    pub fn probe_untranslated_rhs(x: u32) -> u32 {
        let mut y = 0u32;
        y = x;
        y
    }
"#;

const SOURCE_ARG_REF_ONLY: &str = r#"
    #![allow(dead_code, unused_assignments, unused_variables)]

    pub fn probe_arg_ref_only(x: u32) {
        let r = &x;
        let _ = r;
    }
"#;

const SOURCE_PROJECTION_ONLY: &str = r#"
    #![allow(dead_code, unused_assignments, unused_variables)]

    pub struct Pair { pub a: u32, pub b: u32 }

    pub fn probe_projection_only(mut p: Pair, v: u32) {
        p.a = v;
    }
"#;

const SOURCE_NESTED_PROJECTION_ONLY: &str = r#"
    #![allow(dead_code, unused_assignments, unused_variables)]

    pub struct Pair { pub a: u32, pub b: u32 }
    pub struct Wrap { pub pair: Pair }

    pub fn probe_nested_projection_only(mut w: Wrap, v: u32) -> u32 {
        w.pair.a = v;
        w.pair.a
    }
"#;

const SOURCE_COPY_THEN_PROJECTION: &str = r#"
    #![allow(dead_code, unused_assignments, unused_variables)]

    pub struct Pair { pub a: u32, pub b: u32 }
    pub struct Wrap { pub pair: Pair }

    pub fn probe_copy_then_projection(mut w: Wrap, q: Wrap, v: u32) -> u32 {
        w = q;
        w.pair.a = v;
        w.pair.a
    }
"#;

const SOURCE_DEREF_PROJECTION: &str = r#"
    #![allow(dead_code)]
    #![allow(unsafe_op_in_unsafe_fn)]

    pub unsafe fn probe_deref_projection(raw: *mut u32, v: u32) {
        *raw = v;
    }
"#;

const SOURCE_LAYOUT_SENSITIVE_TRANSMUTE: &str = r#"
    #![allow(dead_code)]

    pub struct LayoutSrc {
        pub a: u32,
        pub b: u16,
    }

    pub struct LayoutDst {
        pub a: u16,
        pub b: u32,
    }

    #[repr(C)]
    pub struct ReprSrc {
        pub a: u32,
        pub b: u16,
    }

    #[repr(C)]
    pub struct ReprDst {
        pub a: u32,
        pub b: u16,
    }

    pub fn probe_layout_sensitive_transmute(src: LayoutSrc) -> LayoutDst {
        unsafe { std::mem::transmute::<LayoutSrc, LayoutDst>(src) }
    }

    pub fn probe_repr_c_transmute(src: ReprSrc) -> ReprDst {
        unsafe { std::mem::transmute::<ReprSrc, ReprDst>(src) }
    }
"#;

const SOURCE_TRANSMUTE_UNCHECKED_SIZE_MISMATCH: &str = r#"
    #![allow(dead_code, internal_features)]
    #![feature(core_intrinsics)]

    use std::intrinsics::transmute_unchecked;

    pub unsafe fn probe_transmute_unchecked_size_mismatch(x: u32) -> u16 {
        unsafe { transmute_unchecked(x) }
    }
"#;

fn find_simple_copy_assign(body: &rustc_public::mir::Body) -> (usize, usize, usize) {
    for (bb_idx, block) in body.blocks.iter().enumerate() {
        for stmt in &block.statements {
            if let StatementKind::Assign(lhs, Rvalue::Use(op)) = &stmt.kind {
                let Some(src_local) = (match op {
                    Operand::Copy(src) | Operand::Move(src) => Some(src.local),
                    _ => None, // external enum: Operand
                }) else {
                    continue;
                };
                if lhs.projection.is_empty() && lhs.local != src_local {
                    return (bb_idx, lhs.local, src_local);
                }
            }
        }
    }
    panic!("failed to find simple Copy/Move assignment");
}

fn find_simple_copy_assign_stmt(
    body: &rustc_public::mir::Body,
) -> (usize, &rustc_public::mir::Place, &Rvalue, usize, usize) {
    for (bb_idx, block) in body.blocks.iter().enumerate() {
        for stmt in &block.statements {
            if let StatementKind::Assign(lhs, rhs @ Rvalue::Use(op)) = &stmt.kind {
                let Some(src_local) = (match op {
                    Operand::Copy(src) | Operand::Move(src) => Some(src.local),
                    _ => None, // external enum: Operand
                }) else {
                    continue;
                };
                if lhs.projection.is_empty() && lhs.local != src_local {
                    return (bb_idx, lhs, rhs, lhs.local, src_local);
                }
            }
        }
    }
    panic!("failed to find simple Copy/Move assignment statement");
}

fn find_ref_assign_stmt(
    body: &rustc_public::mir::Body,
) -> (usize, &rustc_public::mir::Place, &Rvalue, usize, usize) {
    for (bb_idx, block) in body.blocks.iter().enumerate() {
        for stmt in &block.statements {
            if let StatementKind::Assign(lhs, rhs) = &stmt.kind
                && lhs.projection.is_empty()
            {
                match rhs {
                    Rvalue::Ref(_, _, place) | Rvalue::AddressOf(_, place) => {
                        return (bb_idx, lhs, rhs, lhs.local, place.local);
                    }
                    _ => {}
                }
            }
        }
    }
    panic!("failed to find Ref/AddressOf assignment statement");
}

fn seed_untracked_destination_metadata(
    chc_ctx: &mut ChcCtx<'_, '_>,
    lhs_local: usize,
    src_local: usize,
) {
    chc_ctx.encode.local_expr_env.insert(lhs_local, Expr::bitvec_const(0xdead_beefu32 as u64, 32));
    chc_ctx.encode.local_signedness.insert(lhs_local, true);
    chc_ctx.encode.flattened_field_env.insert((lhs_local, 0), Expr::bitvec_const(7u64, 8));
    chc_ctx
        .ref_resolution
        .ref_targets
        .insert(lhs_local, RefTarget::with_projections(src_local, vec![]));
    chc_ctx.ref_resolution.call_forwarded_raw_ptrs.insert(lhs_local);
    chc_ctx.ref_resolution.const_ref_values.insert(lhs_local, Expr::bitvec_const(0xbeefu64, 32));
    chc_ctx
        .ref_resolution
        .subslice_len
        .insert(lhs_local, Expr::bitvec_const(4u64, crate::codegen_ay::types::POINTER_WIDTH));
    chc_ctx
        .ref_resolution
        .subslice_offset
        .insert(lhs_local, Expr::bitvec_const(2u64, crate::codegen_ay::types::POINTER_WIDTH));
    chc_ctx.ref_resolution.alloc_result_locals.insert(lhs_local);
    chc_ctx.known_alloc_ids.insert(lhs_local, 17);

    let stale_vtable = chc_ctx.capture_known_vtable_discriminant(
        lhs_local,
        Expr::bitvec_const(0x55u64, crate::codegen_ay::types::POINTER_WIDTH),
    );
    assert!(stale_vtable.is_some(), "test setup requires stale destination vtable metadata");
    let src_vtable = chc_ctx.capture_known_vtable_discriminant(
        src_local,
        Expr::bitvec_const(0x77u64, crate::codegen_ay::types::POINTER_WIDTH),
    );
    assert!(src_vtable.is_some(), "test setup requires source vtable metadata");
}

fn assert_untracked_destination_cleanup(
    chc_ctx: &ChcCtx<'_, '_>,
    lhs_local: usize,
    modified: &HashSet<usize>,
    constraints: &[Expr],
) {
    assert!(!modified.contains(&lhs_local), "untracked dest should not be marked modified");
    // Encode side tables
    assert!(!chc_ctx.encode.local_expr_env.contains_key(&lhs_local), "stale local_expr_env");
    assert!(!chc_ctx.encode.local_signedness.contains_key(&lhs_local), "stale local_signedness");
    assert!(!chc_ctx.encode.flattened_field_env.contains_key(&(lhs_local, 0)), "stale field_env");
    // Ref resolution side tables
    let rr = &chc_ctx.ref_resolution;
    assert!(!rr.ref_targets.contains_key(&lhs_local), "stale ref_targets");
    assert!(!rr.call_forwarded_raw_ptrs.contains(&lhs_local), "stale raw-ptr forwarding");
    assert!(!rr.const_ref_values.contains_key(&lhs_local), "stale const_ref_values");
    assert!(!rr.subslice_len.contains_key(&lhs_local), "stale subslice_len");
    assert!(!rr.subslice_offset.contains_key(&lhs_local), "stale subslice_offset");
    assert!(!rr.alloc_result_locals.contains(&lhs_local), "stale alloc_result_locals");
    // Allocation and vtable
    assert!(!chc_ctx.known_alloc_ids.contains_key(&lhs_local), "stale alloc identity");
    assert!(!chc_ctx.dyn_vtable_ids.contains_key(&lhs_local), "stale vtable metadata");
    assert!(constraints.is_empty(), "unexpected side-channel constraints: {constraints:?}");
}

fn find_projection_assign_local(body: &rustc_public::mir::Body) -> (usize, usize) {
    for (bb_idx, block) in body.blocks.iter().enumerate() {
        for stmt in &block.statements {
            if let StatementKind::Assign(lhs, _rhs) = &stmt.kind
                && !lhs.projection.is_empty()
            {
                return (bb_idx, lhs.local);
            }
        }
    }
    panic!("failed to find projection assignment");
}

fn find_nested_projection_assign_local(body: &rustc_public::mir::Body) -> (usize, usize) {
    for (bb_idx, block) in body.blocks.iter().enumerate() {
        for stmt in &block.statements {
            if let StatementKind::Assign(lhs, _rhs) = &stmt.kind
                && lhs.projection.iter().filter(|p| matches!(p, ProjectionElem::Field(..))).count()
                    >= 2
            {
                return (bb_idx, lhs.local);
            }
        }
    }
    panic!("failed to find nested projection assignment");
}

fn find_copy_then_projection_chain(body: &rustc_public::mir::Body) -> (usize, usize, usize) {
    fn operand_source_local(op: &Operand) -> Option<usize> {
        match op {
            Operand::Copy(src) | Operand::Move(src) => Some(src.local),
            _ => None, // external enum: Operand
        }
    }
    fn rvalue_source_local(rhs: &Rvalue) -> Option<usize> {
        match rhs {
            Rvalue::Use(op) => operand_source_local(op),
            Rvalue::Aggregate(_, ops) => ops.iter().find_map(operand_source_local),
            _ => None, // external enum: Rvalue
        }
    }

    for (bb_idx, block) in body.blocks.iter().enumerate() {
        let mut seen_sources: Vec<(usize, usize)> = Vec::new();
        for stmt in &block.statements {
            if let StatementKind::Assign(lhs, _rhs) = &stmt.kind
                && !lhs.projection.is_empty()
                && let Some((_, src_local)) =
                    seen_sources.iter().rev().find(|(dst, _)| *dst == lhs.local)
            {
                return (bb_idx, lhs.local, *src_local);
            }

            if let StatementKind::Assign(lhs, rhs) = &stmt.kind
                && let Some(src_local) = rvalue_source_local(rhs)
                && lhs.local != src_local
            {
                seen_sources.push((lhs.local, src_local));
            }
        }
    }
    let mut dump = String::new();
    for (bb_idx, block) in body.blocks.iter().enumerate() {
        dump.push_str(&format!("bb{bb_idx}:\n"));
        for (stmt_idx, stmt) in block.statements.iter().enumerate() {
            dump.push_str(&format!("  {stmt_idx}: {:?}\n", stmt.kind));
        }
    }
    panic!("failed to find copy-then-projection assignment chain\n{dump}");
}

fn find_transmute_cast(
    body: &rustc_public::mir::Body,
) -> (rustc_public::mir::Operand, rustc_public::ty::Ty) {
    for block in &body.blocks {
        for stmt in &block.statements {
            if let StatementKind::Assign(
                _lhs,
                Rvalue::Cast(rustc_public::mir::CastKind::Transmute, operand, target_ty),
            ) = &stmt.kind
            {
                return (operand.clone(), *target_ty);
            }
        }
    }
    panic!("failed to find CastKind::Transmute assignment");
}

#[test]
fn test_unsupported_rvalue_fallback_increments_counter() {
    with_test_ay_ctx_for_source(SOURCE_COPY_ASSIGN, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_untranslated_rhs");
        let body = instance.body().expect("function body");
        let mut chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "probe_untranslated_rhs", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let (bb_idx, lhs_local, src_local) = find_simple_copy_assign(&body);
        chc_ctx.state_var_mgr.local_to_state_idx.remove(&src_local);

        let before = chc_ctx.fallback_count;
        let (_constraints, _output_args, modified, _safety_checks) =
            chc_ctx.encode_block_statements(bb_idx);
        let after = chc_ctx.fallback_count;

        assert!(
            after > before,
            "unsupported rvalue fallback should increment fallback_count (before={before}, after={after})"
        );
        assert!(
            modified.contains(&lhs_local),
            "unsupported rvalue fallback should mark destination local as modified"
        );
    });
}

#[test]
fn test_simple_assignment_untracked_destination_increments_sound_fallback_counter() {
    with_test_ay_ctx_for_source(SOURCE_COPY_ASSIGN, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_untranslated_rhs");
        let body = instance.body().expect("function body");
        let mut chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "probe_untranslated_rhs", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let (bb_idx, lhs, rhs, lhs_local, src_local) = find_simple_copy_assign_stmt(&body);
        let removed = chc_ctx.state_var_mgr.local_to_state_idx.remove(&lhs_local);
        assert!(removed.is_some(), "test setup requires tracked destination local {lhs_local}");
        seed_untracked_destination_metadata(&mut chc_ctx, lhs_local, src_local);

        let rhs_expr = chc_ctx
            .translate_rvalue_with_modified(rhs, &HashSet::new(), Some(lhs_local))
            .expect("rhs translation should succeed when only the destination local is untracked");
        let mut constraints = Vec::new();
        let mut last_constraint = std::collections::HashMap::new();
        let mut modified = HashSet::new();

        let before = chc_ctx.sound_fallback_count();
        {
            let mut acc = super::super::stmt_accumulator::StmtAccumulator::new(
                &mut modified,
                &mut constraints,
                &mut last_constraint,
            );
            chc_ctx.encode_simple_assignment(lhs, rhs, rhs_expr, lhs_local, bb_idx, &mut acc);
        }
        let after = chc_ctx.sound_fallback_count();

        assert!(
            after > before,
            "untracked simple-assignment destination should increment sound_fallback_count \
             (before={before}, after={after})"
        );
        assert_untracked_destination_cleanup(&chc_ctx, lhs_local, &modified, &constraints);
    });
}

#[test]
fn test_ref_assignment_untracked_referent_increments_sound_fallback_counter() {
    with_test_ay_ctx_for_source(SOURCE_ARG_REF_ONLY, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_arg_ref_only");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            "probe_arg_ref_only",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );
        chc_ctx.declare_block_relations();

        let (bb_idx, lhs, rhs, dest_local, referent_local) = find_ref_assign_stmt(&body);
        let removed = chc_ctx.state_var_mgr.local_to_state_idx.remove(&referent_local);
        assert!(removed.is_some(), "test setup requires tracked referent local {referent_local}");

        let rhs_expr = chc_ctx
            .translate_rvalue_with_modified(rhs, &HashSet::new(), Some(dest_local))
            .expect("Ref rhs translation should still produce an address expression");
        let mut constraints = Vec::new();
        let mut last_constraint = std::collections::HashMap::new();
        let mut modified = HashSet::new();

        let before = chc_ctx.sound_fallback_count();
        {
            let mut acc = super::super::stmt_accumulator::StmtAccumulator::new(
                &mut modified,
                &mut constraints,
                &mut last_constraint,
            );
            chc_ctx.encode_simple_assignment(lhs, rhs, rhs_expr, dest_local, bb_idx, &mut acc);
        }
        let after = chc_ctx.sound_fallback_count();

        assert!(
            after > before,
            "ref assignment with untracked referent should increment sound_fallback_count \
             (before={before}, after={after})"
        );
        assert!(
            modified.contains(&dest_local),
            "tracked destination ref local should still be marked modified"
        );
    });
}

#[test]
fn test_flattened_field_projection_sort_mismatch_increments_counter() {
    with_test_ay_ctx_for_source(SOURCE_PROJECTION_ONLY, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_projection_only");
        let body = instance.body().expect("function body");
        let mut chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "probe_projection_only", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let (bb_idx, local_idx) = find_projection_assign_local(&body);
        chc_ctx.flatten.flattened_tuple_locals.insert(local_idx);
        let vec_idx = chc_ctx.state_idx_for_local(local_idx);
        let (slot_name, _slot_sort) = chc_ctx.state_var_mgr.output_state_vars[vec_idx].clone();
        // Use Array(Int, Int) — no coercion path from BV32 to this sort.
        // Array(BV32, BV32) was accidentally handled by reinterpret_fixed_layout_expr (#3675).
        let bad_sort = Sort::array(Sort::int(), Sort::int());
        chc_ctx.state_var_mgr.output_state_vars[vec_idx] = (slot_name, bad_sort);

        let before = chc_ctx.sound_fallback_count();
        let (_constraints, _output_args, _modified, _safety_checks) =
            chc_ctx.encode_block_statements(bb_idx);
        let after = chc_ctx.sound_fallback_count();

        assert!(
            after > before,
            "flattened field projection sort mismatch should increment fallback_count \
             (before={before}, after={after})"
        );
    });
}

#[test]
fn test_projection_assignment_with_unsupported_projection_increments_counter() {
    with_test_ay_ctx_for_source(SOURCE_DEREF_PROJECTION, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_deref_projection");
        let body = instance.body().expect("function body");
        let mut chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "probe_deref_projection", ChcConfig::default());
        chc_ctx.declare_block_relations();

        // Ensure Deref projection is not handled by ref_targets path.
        chc_ctx.ref_resolution.ref_targets.clear();
        chc_ctx.ref_resolution.ref_arg_pointee_idx.clear();

        let (bb_idx, local_idx) = find_projection_assign_local(&body);
        let has_deref_proj = body.blocks[bb_idx].statements.iter().any(|stmt| {
            if let StatementKind::Assign(lhs, _rhs) = &stmt.kind
                && lhs.local == local_idx
            {
                return lhs.projection.iter().any(|p| matches!(p, ProjectionElem::Deref));
            }
            false
        });
        assert!(
            has_deref_proj,
            "test setup must target a Deref projection assignment for unsupported-projection path"
        );

        // Part of #3561: Deref projection stores to raw pointers are now handled
        // precisely through the Mem-level store handler, even without ref_targets
        // resolution. The fallback is no longer triggered for this case.
        // (Previously Part of #3459: was DEMOTED→SOUND fallback.)
        let before = chc_ctx.sound_fallback_count();
        let (_constraints, _output_args, _modified, _safety_checks) =
            chc_ctx.encode_block_statements(bb_idx);
        let after = chc_ctx.sound_fallback_count();

        assert!(
            after == before,
            "raw pointer deref store should now be handled precisely (no fallback), \
             but sound_fallback_count changed: before={before}, after={after}"
        );
    });
}

#[test]
fn test_projection_root_output_lookup_failure_increments_counter() {
    with_test_ay_ctx_for_source(SOURCE_COPY_THEN_PROJECTION, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_copy_then_projection");
        let body = instance.body().expect("function body");
        let mut chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "probe_copy_then_projection", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let (bb_idx, dst_local, src_local) = find_copy_then_projection_chain(&body);
        chc_ctx.flatten.flattened_tuple_locals.remove(&dst_local);
        // First statement in chain: force unsupported-rvalue fallback, which marks dst
        // modified and clears its env expression.
        chc_ctx.state_var_mgr.local_to_state_idx.remove(&src_local);
        // Second statement in chain: when reading root_in for modified dst local,
        // force output_state_vars lookup failure to hit line 398 path.
        chc_ctx.state_var_mgr.local_to_state_idx.insert(dst_local, usize::MAX / 2);

        let before = chc_ctx.sound_fallback_count();
        let (_constraints, _output_args, modified, _safety_checks) =
            chc_ctx.encode_block_statements(bb_idx);
        let after = chc_ctx.sound_fallback_count();

        assert!(
            modified.contains(&dst_local),
            "setup requires first assignment fallback to mark destination local modified"
        );
        // Part of #3099: unsupported rhs increments sound_fallback_count (sound
        // over-approximation). Missing output slot triggers the self-loop handler
        // which increments fallback_count (unsound — kept intentionally).
        assert!(
            after > before,
            "unsupported rhs fallback should increment sound_fallback_count \
             (before={before}, after={after})"
        );
        assert!(
            chc_ctx.fallback_count >= 1,
            "missing output slot should trigger self-loop handler and increment fallback_count \
             (fallback_count={})",
            chc_ctx.fallback_count
        );
    });
}

#[test]
fn test_projection_root_state_lookup_failure_increments_counter() {
    with_test_ay_ctx_for_source(SOURCE_NESTED_PROJECTION_ONLY, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_nested_projection_only");
        let body = instance.body().expect("function body");
        let mut chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "probe_nested_projection_only", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let (bb_idx, local_idx) = find_nested_projection_assign_local(&body);
        chc_ctx.flatten.flattened_tuple_locals.remove(&local_idx);
        chc_ctx.state_var_mgr.local_to_state_idx.insert(local_idx, usize::MAX / 2);

        // Part of #3369: reclassified from sound_fallback to fallback (DEMOTED) —
        // missing input state var means local keeps identity, not nondeterministic.
        let before = chc_ctx.fallback_count;
        let (_constraints, _output_args, _modified, _safety_checks) =
            chc_ctx.encode_block_statements(bb_idx);
        let after = chc_ctx.fallback_count;

        assert!(
            after > before,
            "missing state_vars root lookup should increment fallback_count \
             (before={before}, after={after})"
        );
    });
}

#[test]
fn test_projection_root_non_datatype_increments_counter() {
    with_test_ay_ctx_for_source(SOURCE_NESTED_PROJECTION_ONLY, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_nested_projection_only");
        let body = instance.body().expect("function body");
        let mut chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "probe_nested_projection_only", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let (bb_idx, local_idx) = find_nested_projection_assign_local(&body);
        chc_ctx.flatten.flattened_tuple_locals.remove(&local_idx);
        let vec_idx = chc_ctx.state_idx_for_local(local_idx);
        let (name, _sort) = chc_ctx.state_var_mgr.state_vars[vec_idx].clone();
        chc_ctx.state_var_mgr.state_vars[vec_idx] = (name, Sort::bitvec(32));

        let before = chc_ctx.sound_fallback_count();
        let (_constraints, _output_args, _modified, _safety_checks) =
            chc_ctx.encode_block_statements(bb_idx);
        let after = chc_ctx.sound_fallback_count();

        assert!(
            after > before,
            "projection root non-datatype path should increment fallback_count \
             (before={before}, after={after})"
        );
    });
}

#[test]
fn test_layout_sensitive_cross_adt_transmute_records_sound_fallback() {
    with_test_ay_ctx_for_source(SOURCE_LAYOUT_SENSITIVE_TRANSMUTE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_layout_sensitive_transmute");
        let body = instance.body().expect("function body");
        let mut chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "probe_layout_sensitive_transmute", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let (operand, target_ty) = find_transmute_cast(&body);
        let target_sort = ChcCtx::translate_ty(target_ty).expect("target sort for LayoutDst");
        let modified = HashSet::<usize>::new();

        assert_eq!(
            chc_ctx.sound_fallback_count(),
            0,
            "precondition: test starts with zero sound fallbacks"
        );

        let result = chc_ctx
            .translate_rvalue_cast(
                &rustc_public::mir::CastKind::Transmute,
                &operand,
                &target_ty,
                &modified,
            )
            .expect("layout-sensitive transmute should still produce a target expression");

        assert_eq!(
            *result.sort(),
            target_sort,
            "layout-sensitive transmute fallback should preserve the destination sort"
        );
        assert_eq!(
            chc_ctx.sound_fallback_count(),
            1,
            "layout-sensitive cross-ADT transmute should record one sound fallback"
        );
        assert!(
            result.to_string().contains("__transmute_layout_nondet"),
            "layout-sensitive transmute should use a fresh nondeterministic fallback, got {result}"
        );
    });
}

#[test]
fn test_repr_c_cross_adt_transmute_stays_precise() {
    with_test_ay_ctx_for_source(SOURCE_LAYOUT_SENSITIVE_TRANSMUTE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_repr_c_transmute");
        let body = instance.body().expect("function body");
        let mut chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "probe_repr_c_transmute", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let (operand, target_ty) = find_transmute_cast(&body);
        let target_sort = ChcCtx::translate_ty(target_ty).expect("target sort for ReprDst");
        let modified = HashSet::<usize>::new();

        let result = chc_ctx
            .translate_rvalue_cast(
                &rustc_public::mir::CastKind::Transmute,
                &operand,
                &target_ty,
                &modified,
            )
            .expect("repr(C) cross-ADT transmute should stay on the precise path");

        assert_eq!(
            *result.sort(),
            target_sort,
            "repr(C) transmute should preserve the destination sort"
        );
        assert_eq!(
            chc_ctx.sound_fallback_count(),
            0,
            "repr(C) cross-ADT transmute should avoid sound fallback"
        );
        assert!(
            !result.to_string().contains("__transmute_layout_nondet"),
            "repr(C) transmute should not become nondeterministic: {result}"
        );
    });
}

#[test]
fn test_transmute_unchecked_size_mismatch_emits_ub_and_accounted_havoc() {
    with_test_ay_ctx_for_source(SOURCE_TRANSMUTE_UNCHECKED_SIZE_MISMATCH, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_transmute_unchecked_size_mismatch");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            "probe_transmute_unchecked_size_mismatch",
            ChcConfig::default(),
        );
        chc_ctx.declare_block_relations();

        let (operand, target_ty) = find_transmute_cast(&body);
        let modified = HashSet::<usize>::new();
        let result = chc_ctx
            .translate_rvalue_cast(
                &rustc_public::mir::CastKind::Transmute,
                &operand,
                &target_ty,
                &modified,
            )
            .expect("size-mismatched transmute should produce an accounted havoc value");

        assert!(
            result.to_string().contains("__transmute_size_mismatch_ub"),
            "size-mismatched transmute must not flow through a precise coercion: {result}"
        );
        assert_eq!(
            chc_ctx.heap_state.pending_checks.iter().map(ToString::to_string).collect::<Vec<_>>(),
            vec!["false"],
            "reaching transmute_unchecked with unequal layouts is unconditional UB"
        );
        assert_eq!(
            chc_ctx.sound_fallback_count(),
            1,
            "the destination havoc must remain a sound-approximation event"
        );
        assert_eq!(
            chc_ctx.vc.accounted_approximations, 1,
            "Task #78 must account for the havoc before counterexample recertification"
        );
    });
}

// =============================================================================
// Part of #2783: Assume guard + flatten missing output slot fallback paths
// =============================================================================

const SOURCE_ASSUME: &str = r#"
    #![allow(dead_code)]
    #![allow(internal_features)]
    #![feature(core_intrinsics)]

    pub fn probe_intrinsic_assume_fallback(cond: bool, x: u32) -> u32 {
        unsafe { core::intrinsics::assume(cond); }
        x.wrapping_add(1)
    }
"#;

/// Intrinsic::Assume with untranslatable condition must increment fallback_count.
/// Exercises codegen_stmt.rs line 132.
/// Part of #2783.
#[test]
fn test_assume_guard_untranslatable_increments_counter() {
    with_test_ay_ctx_for_source(SOURCE_ASSUME, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_intrinsic_assume_fallback");
        let body = instance.body().expect("function body");
        let mut chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "probe_intrinsic_assume_fallback", ChcConfig::default());
        chc_ctx.declare_block_relations();

        // Find the block containing the Assume intrinsic
        let assume_bb_idx = body
            .blocks
            .iter()
            .enumerate()
            .find_map(|(bb_idx, bb)| {
                bb.statements
                    .iter()
                    .any(|stmt| {
                        matches!(
                            stmt.kind,
                            StatementKind::Intrinsic(
                                rustc_public::mir::NonDivergingIntrinsic::Assume(_)
                            )
                        )
                    })
                    .then_some(bb_idx)
            })
            .expect("MIR should contain an Intrinsic::Assume statement");

        // Find the condition local from the Assume operand, then remove it
        // from local_to_state_idx so translate_operand_with_modified returns None.
        for stmt in &body.blocks[assume_bb_idx].statements {
            if let StatementKind::Intrinsic(rustc_public::mir::NonDivergingIntrinsic::Assume(op)) =
                &stmt.kind
            {
                if let Operand::Copy(place) | Operand::Move(place) = op {
                    chc_ctx.state_var_mgr.local_to_state_idx.remove(&place.local);
                }
                break;
            }
        }

        // Part of #3099: Dropped assume is SOUND_APPROXIMATION (over-approximation:
        // explores more state space). Verify sound_fallback_count increments, not
        // fallback_count (DEMOTED).
        let before = chc_ctx.sound_fallback_count();
        let (_constraints, _output_args, _modified, _safety_checks) =
            chc_ctx.encode_block_statements(assume_bb_idx);
        let after = chc_ctx.sound_fallback_count();

        assert!(
            after > before,
            "Intrinsic::Assume with untranslatable condition should increment sound_fallback_count \
             (before={before}, after={after})"
        );
    });
}

/// Regression guard: Int rhs assigned into BitVec output should NOT increment
/// fallback_count now that assignment coercion supports Int->BitVec.
/// Part of #2783.
#[test]
fn test_sort_mismatch_bitvec_output_increments_counter() {
    with_test_ay_ctx_for_source(SOURCE_COPY_ASSIGN, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_untranslated_rhs");
        let body = instance.body().expect("function body");
        let mut chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "probe_untranslated_rhs", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let (_bb_idx, lhs_local, src_local) = find_simple_copy_assign(&body);

        // Corrupt source local's state_var sort to Int so the translated operand
        // produces an Int expression while destination remains BitVec(32).
        // Assignment path should now coerce Int->BitVec without symbolic fallback.
        let src_vec_idx = chc_ctx.state_idx_for_local(src_local);
        let (src_name, _src_sort) = chc_ctx.state_var_mgr.state_vars[src_vec_idx].clone();
        chc_ctx.state_var_mgr.state_vars[src_vec_idx] = (src_name, Sort::int());

        // Ensure output sort for lhs is bitvec
        let lhs_vec_idx = chc_ctx.state_idx_for_local(lhs_local);
        assert!(
            chc_ctx.state_var_mgr.output_state_vars[lhs_vec_idx].1.bitvec_width().is_some(),
            "test setup: output sort for lhs must be bitvec"
        );

        let before = chc_ctx.sound_fallback_count();
        let (_constraints, _output_args, _modified, _safety_checks) =
            chc_ctx.encode_block_statements(0);
        let after = chc_ctx.sound_fallback_count();

        assert!(
            after == before,
            "int->bitvec assignment coercion should avoid fallback_count increment \
             (before={before}, after={after})"
        );
    });
}

/// Regression guard: BitVec rhs assigned into Int output should NOT increment
/// fallback_count now that assignment coercion supports BitVec->Int.
/// Part of #2783.
#[test]
fn test_sort_mismatch_non_bitvec_output_increments_counter() {
    with_test_ay_ctx_for_source(SOURCE_COPY_ASSIGN, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_untranslated_rhs");
        let body = instance.body().expect("function body");
        let mut chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "probe_untranslated_rhs", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let (_bb_idx, lhs_local, _src_local) = find_simple_copy_assign(&body);

        // Corrupt output sort for lhs to Int (non-bitvec) while rhs stays BitVec(32).
        // Assignment path should now coerce BitVec->Int without symbolic fallback.
        let lhs_vec_idx = chc_ctx.state_idx_for_local(lhs_local);
        let (out_name, _out_sort) = chc_ctx.state_var_mgr.output_state_vars[lhs_vec_idx].clone();
        chc_ctx.state_var_mgr.output_state_vars[lhs_vec_idx] = (out_name, Sort::int());

        let before = chc_ctx.sound_fallback_count();
        let (_constraints, _output_args, _modified, _safety_checks) =
            chc_ctx.encode_block_statements(0);
        let after = chc_ctx.sound_fallback_count();

        assert!(
            after == before,
            "bitvec->int assignment coercion should avoid fallback_count increment \
             (before={before}, after={after})"
        );
    });
}

/// Flattened field with missing output slot must increment fallback_count.
/// Exercises codegen_stmt_flatten.rs line 98 by calling
/// `constrain_flattened_fields` directly with 2 values but only 1 output slot.
/// Part of #2783.
#[test]
fn test_flattened_field_missing_output_slot_increments_counter() {
    with_test_ay_ctx_for_source(SOURCE_COPY_ASSIGN, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_untranslated_rhs");
        let body = instance.body().expect("function body");
        let mut chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "probe_untranslated_rhs", ChcConfig::default());
        chc_ctx.declare_block_relations();

        // Pick local 0 (return value), ensure it's in flattened set
        let local_idx = 0usize;
        chc_ctx.flatten.flattened_tuple_locals.insert(local_idx);
        let vec_idx = chc_ctx.state_idx_for_local(local_idx);

        // Truncate output_state_vars so that vec_idx exists but vec_idx+1 does not.
        chc_ctx.state_var_mgr.output_state_vars.truncate(vec_idx + 1);

        // 2 field values: field 0 fits, field 1 overflows
        let values = vec![
            Some(ay_bindings::Expr::bitvec_const(1, 32)),
            Some(ay_bindings::Expr::bitvec_const(2, 32)),
        ];
        let mut constraints = Vec::new();
        let mut last_constraint = std::collections::HashMap::new();
        let mut modified = HashSet::new();

        let before = chc_ctx.sound_fallback_count();
        let _emitted = {
            let mut acc = super::super::stmt_accumulator::StmtAccumulator::new(
                &mut modified,
                &mut constraints,
                &mut last_constraint,
            );
            chc_ctx.constrain_flattened_fields(local_idx, &values, &mut acc)
        };
        let after = chc_ctx.sound_fallback_count();

        assert!(
            after > before,
            "flattened field with missing output slot should increment fallback_count \
             (before={before}, after={after})"
        );
    });
}

// =============================================================================
// Part of #2783: CopyNonOverlapping destination-unresolved fallback
// =============================================================================

const SOURCE_COPY_NONOVERLAPPING: &str = r#"
    #![allow(dead_code)]
    use std::ptr;

    pub fn probe_copy_nonoverlapping_fallback(
        mut dst: [u8; 4], src: [u8; 4], count: usize,
    ) -> [u8; 4] {
        unsafe {
            ptr::copy_nonoverlapping(src.as_ptr(), dst.as_mut_ptr(), count);
        }
        dst
    }
"#;

/// CopyNonOverlapping with unresolvable destination must increment fallback_count.
/// Exercises codegen_stmt.rs line 149 — the `!handled` branch after
/// `try_encode_copy_nonoverlapping_intrinsic` returns false.
///
/// Production site: codegen_stmt.rs line 149.
/// Part of #2783.
#[test]
fn test_copy_nonoverlapping_unresolvable_dst_increments_fallback_counter() {
    with_test_ay_ctx_for_source(SOURCE_COPY_NONOVERLAPPING, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_copy_nonoverlapping_fallback");
        let body = instance.body().expect("function body");
        let mut chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "probe_copy_nonoverlapping_fallback", ChcConfig::default());
        chc_ctx.declare_block_relations();

        // Find the block containing the CopyNonOverlapping intrinsic statement.
        // MIR may lower copy_nonoverlapping as a call terminator instead of an
        // intrinsic statement depending on compiler version and optimization;
        // skip if the intrinsic statement form is not present.
        let copy_bb_idx = body.blocks.iter().enumerate().find_map(|(bb_idx, bb)| {
            bb.statements
                .iter()
                .any(|stmt| {
                    matches!(
                        stmt.kind,
                        StatementKind::Intrinsic(NonDivergingIntrinsic::CopyNonOverlapping(_))
                    )
                })
                .then_some(bb_idx)
        });

        let Some(copy_bb_idx) = copy_bb_idx else {
            // MIR lowered copy_nonoverlapping as a call terminator, not an
            // intrinsic statement. The call-level fallback is covered by
            // test_call_ptr.rs::test_copy_nonoverlapping_short_args_increments_fallback_counter.
            return;
        };

        // Clear ref_targets so resolve_copy_intrinsic_target_local returns None
        // for the destination operand. try_encode_copy_nonoverlapping_intrinsic
        // returns false → encode_block_statements calls record_sound_fallback().
        // Part of #3099: reclassified from record_fallback() to record_sound_fallback()
        // because the statement is simply dropped (destination retains universally-
        // quantified input value — sound over-approximation).
        chc_ctx.ref_resolution.ref_targets.clear();

        let before = chc_ctx.sound_fallback_count();
        let (_constraints, _output_args, _modified, _safety_checks) =
            chc_ctx.encode_block_statements(copy_bb_idx);
        let after = chc_ctx.sound_fallback_count();

        assert!(
            after > before,
            "CopyNonOverlapping with unresolvable destination should increment \
             sound_fallback_count (before={before}, after={after})"
        );
    });
}
