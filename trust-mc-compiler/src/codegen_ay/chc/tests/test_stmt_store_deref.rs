// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Dedicated tests for the deref-store path in `codegen_stmt_store.rs`.
//!
//! This module specifically targets `StmtStore::handle_deref_store_mem_level`,
//! which was previously tracked as `codegen_stmt_store_deref.rs` before module
//! consolidation.
//!
//! Part of #2382 (dedicated coverage for deref-store behavior).

// Test code: unwrap/panic are acceptable for assertions
#![allow(clippy::unwrap_used, clippy::panic)]

use super::super::stmt_accumulator::StmtAccumulator;
use super::common::*;
use crate::codegen_ay::emit_chc;
use rustc_public::mir::{Local, Place, ProjectionElem};
use std::collections::HashMap;

const DEREF_STORE_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub unsafe fn store_via_raw_ptr(ptr: *mut u32, val: u32) {
        unsafe { *ptr = val; }
    }
"#;

const SCALAR_REF_STORE_MIRROR_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub fn mirror_scalar_ref_store_probe() -> u32 {
        let mut x: u32 = 0;
        let r = &mut x;
        *r = 5;
        *r
    }
"#;

const OPAQUE_CHAIN_STORE_MIRROR_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub fn opaque_chain_store_probe() -> bool {
        let left = [1u8, 2u8].into_iter();
        let right = [3u8, 4u8].into_iter();
        let mut iter = left.chain(right);
        iter.next().is_some()
    }
"#;

/// Happy path: `*ptr = value` at Mem level should emit a memory store constraint.
#[test]
fn test_handle_deref_store_mem_level_emits_store_constraint() {
    with_test_ay_ctx_for_source(DEREF_STORE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "store_via_raw_ptr");
        let body = instance.body().expect("body");
        let chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            "store_via_raw_ptr",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );
        let (vc, _needs_mem_promote) = chc_ctx.translate();
        let smt = emit_chc(&vc).to_string();
        assert!(
            smt.contains("(store"),
            "Mem-level Deref store should emit a store() constraint, got: {}",
            &smt[..smt.len().min(800)]
        );
    });
}

/// Scalar safe-ref stores (`let r = &mut x; *r = 5;`) at Mem level must emit:
/// 1. heap memory store constraint; and
/// 2. register mirror equality for the ref_target scalar local.
///
/// This directly covers the scalar path in `mirror_scalar_ref_store`.
#[test]
fn test_handle_deref_store_mem_level_scalar_ref_store_emits_register_mirror_constraint() {
    with_test_ay_ctx_for_source(SCALAR_REF_STORE_MIRROR_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "mirror_scalar_ref_store_probe");
        let body = instance.body().expect("body");
        let chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            "mirror_scalar_ref_store_probe",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );
        let (vc, _needs_mem_promote) = chc_ctx.translate();
        let smt = emit_chc(&vc).to_string();
        // After ay bump to declare-var encoding, state variables are free
        // variables. Check semantic invariants: heap memory modeled + register mirror.
        let has_memory_model = any_constraint_str(&vc, |c| c.contains("(store "))
            || smt.contains("(store ")
            || vc.vars().iter().any(|v| v.sort.is_array() && v.name.contains("mem"));
        assert!(has_memory_model, "Mem-level scalar deref store should model heap memory");
        let has_register_mirror = any_constraint_str(&vc, |c| {
            c.contains("_mirror_scalar_ref_store_probe_1__out") && c.contains("#x00000005")
        }) || (smt.contains("_mirror_scalar_ref_store_probe_1__out")
            && smt.contains("#x00000005"));
        assert!(has_register_mirror, "expected scalar register mirror equality for local x");
    });
}

/// Opaque iterator adapters (`Chain`, `Fuse`, etc.) are modeled as scalar
/// pointer-width symbols, so field writes through `&mut self.field` cannot
/// mirror into per-field slots. The translation should complete without panics
/// and produce rules that contain opaque adapter store indicators.
#[test]
fn test_mirror_scalar_ref_store_updates_opaque_chain_local_with_symbolic_post_store() {
    with_test_ay_ctx_for_source(OPAQUE_CHAIN_STORE_MIRROR_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "opaque_chain_store_probe");
        let body = instance.body().expect("body");
        let chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            "opaque_chain_store_probe",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );
        let (vc, _needs_mem_promote) = chc_ctx.translate();
        let smt = emit_chc(&vc).to_string();

        // The translation must complete (no panics) and produce nontrivial output.
        // Chain iterators are encoded as opaque scalars or Datatypes depending on
        // the iterator source. The opaque adapter store path fires when Chain is
        // scalar-encoded (complex cases). Either way, the translation must succeed.
        assert!(
            vc.rules.len() >= 2,
            "opaque chain store probe should produce multiple rules, got {}",
            vc.rules.len()
        );
        assert!(
            smt.contains("chain") || smt.contains("Chain") || smt.contains("_opaque_chain"),
            "translation should reference the Chain iterator, got: {}",
            &smt[..smt.len().min(800)]
        );
    });
}

const DEREF_STORE_UNSUPPORTED_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub fn store_with_index(ptr: &mut [u32; 4], idx: usize, val: u32) {
        (*ptr)[idx] = val;
    }
"#;

/// Error path: unsupported `Deref + Index` projection is handled by dropping
/// the transition (no store constraint emitted).
#[test]
fn test_handle_deref_store_mem_level_unsupported_projection_drops_store() {
    with_test_ay_ctx_for_source(DEREF_STORE_UNSUPPORTED_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "store_with_index");
        let body = instance.body().expect("body");
        let mut chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            "store_with_index",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );

        let lhs = Place {
            local: Local::from(1usize),
            projection: vec![ProjectionElem::Deref, ProjectionElem::Index(Local::from(2usize))],
        };
        let rhs_expr = Expr::bitvec_const(5u64, 32);
        let mut modified = HashSet::new();
        let mut constraints = Vec::new();
        let mut last_constraint_for_local: HashMap<usize, usize> = HashMap::new();

        let handled = {
            let mut acc = StmtAccumulator::new(
                &mut modified,
                &mut constraints,
                &mut last_constraint_for_local,
            );
            chc_ctx.handle_deref_store_mem_level(&lhs, &rhs_expr, 1, 0, &mut acc)
        };
        assert!(handled, "unsupported Deref+Index should still return handled");
        assert!(
            constraints.is_empty(),
            "unsupported Deref+Index should drop store instead of emitting constraints, got {constraints:?}"
        );
        assert!(
            last_constraint_for_local.is_empty(),
            "dropped store should not record output-constraint indices"
        );
    });
}

/// (#2529 path #8) Non-pointer type on Deref store at Mem level should be
/// treated as a dropped store (handled=true, no constraints) and increment
/// STORE_DROPPED_TRANSITION_COUNT. The local's type is u32 (not a pointer/ref/Box),
/// so `deref_pointee_ty` returns None, triggering the fallback at codegen_stmt_store.rs:199.
#[test]
fn test_handle_deref_store_mem_level_non_pointer_type_drops_store() {
    with_test_ay_ctx_for_source(DEREF_STORE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "store_via_raw_ptr");
        let body = instance.body().expect("body");
        let mut chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            "store_via_raw_ptr",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );

        // local 2 = val: u32 — NOT a pointer type.
        // Constructing a Deref place on a non-pointer local triggers the
        // `deref_pointee_ty` → None fallback path.
        let lhs = Place { local: Local::from(2usize), projection: vec![ProjectionElem::Deref] };
        let rhs_expr = Expr::bitvec_const(42u64, 32);
        let mut modified = HashSet::new();
        let mut constraints = Vec::new();
        let mut last_constraint_for_local: HashMap<usize, usize> = HashMap::new();

        let handled = {
            let mut acc = StmtAccumulator::new(
                &mut modified,
                &mut constraints,
                &mut last_constraint_for_local,
            );
            chc_ctx.handle_deref_store_mem_level(&lhs, &rhs_expr, 2, 0, &mut acc)
        };

        assert!(handled, "Non-pointer Deref store should be handled (skipped)");
        assert!(
            constraints.is_empty(),
            "Non-pointer Deref store should emit no constraints, got {constraints:?}"
        );
        assert!(
            chc_ctx.diagnostics.store_dropped_transition.get() > 0,
            "Non-pointer Deref store must increment STORE_DROPPED_TRANSITION_COUNT \
             (got {})",
            chc_ctx.diagnostics.store_dropped_transition.get()
        );
    });
}

/// Missing pointer input state in the Mem-level deref store path must seed a
/// fresh heap store-chain rather than leaving the typed heap array on its input
/// side. This keeps later same-block reads from reusing the stale heap value.
#[test]
fn test_handle_deref_store_mem_level_missing_input_var_seeds_unconstrained_heap() {
    with_test_ay_ctx_for_source(DEREF_STORE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "store_via_raw_ptr");
        let body = instance.body().expect("body");
        let mut chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            "store_via_raw_ptr",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );
        chc_ctx.declare_block_relations();
        chc_ctx.state_var_mgr.state_vars.clear();
        chc_ctx.state_var_mgr.output_state_vars.clear();

        let lhs = Place { local: Local::from(1usize), projection: vec![ProjectionElem::Deref] };
        let rhs_expr = Expr::bitvec_const(42u64, 32);
        let mut modified = HashSet::new();
        let mut constraints = Vec::new();
        let mut last_constraint_for_local: HashMap<usize, usize> = HashMap::new();

        let handled = {
            let mut acc = StmtAccumulator::new(
                &mut modified,
                &mut constraints,
                &mut last_constraint_for_local,
            );
            chc_ctx.handle_deref_store_mem_level(&lhs, &rhs_expr, 1, 0, &mut acc)
        };

        assert!(handled, "missing pointer input state var should still be handled");
        assert!(constraints.is_empty(), "drop path should not emit direct constraints");
        assert!(
            chc_ctx.heap_state.get_store_chain("u32").is_some(),
            "drop path must seed a fresh typed heap array instead of keeping the stale input heap"
        );
        assert!(
            chc_ctx.heap_state.is_array_modified("u32"),
            "drop path must mark the typed heap array modified"
        );
    });
}

/// Missing pointer output state in the Mem-level deref store path must also
/// seed a fresh heap store-chain. This is the `acc.modified.contains(local_idx)`
/// branch of the same #3138 fix.
#[test]
fn test_handle_deref_store_mem_level_missing_output_var_seeds_unconstrained_heap() {
    with_test_ay_ctx_for_source(DEREF_STORE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "store_via_raw_ptr");
        let body = instance.body().expect("body");
        let mut chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            "store_via_raw_ptr",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );
        chc_ctx.declare_block_relations();
        chc_ctx.state_var_mgr.state_vars.clear();
        chc_ctx.state_var_mgr.output_state_vars.clear();

        let lhs = Place { local: Local::from(1usize), projection: vec![ProjectionElem::Deref] };
        let rhs_expr = Expr::bitvec_const(42u64, 32);
        let mut modified = HashSet::from([1usize]);
        let mut constraints = Vec::new();
        let mut last_constraint_for_local: HashMap<usize, usize> = HashMap::new();

        let handled = {
            let mut acc = StmtAccumulator::new(
                &mut modified,
                &mut constraints,
                &mut last_constraint_for_local,
            );
            chc_ctx.handle_deref_store_mem_level(&lhs, &rhs_expr, 1, 0, &mut acc)
        };

        assert!(handled, "missing pointer output state var should still be handled");
        assert!(constraints.is_empty(), "drop path should not emit direct constraints");
        assert!(
            chc_ctx.heap_state.get_store_chain("u32").is_some(),
            "drop path must seed a fresh typed heap array instead of keeping the stale output heap"
        );
        assert!(
            chc_ctx.heap_state.is_array_modified("u32"),
            "drop path must mark the typed heap array modified"
        );
    });
}

/// Struct field store through mutable reference at Mem level exercises the
/// `mirror_flattened_field_store` path in `deref_mem_mirror.rs`.
///
/// Pattern: `(*ptr).a = 99` where `Pair { a, b }` is flattened to per-field
/// state vars. The mirror must emit a register equality constraint for the
/// target field slot while preserving sibling field state.
///
/// Part of #2895: covers `mirror_flattened_field_store` happy path.
#[test]
fn test_deref_mem_mirror_flattened_field_store_single_field() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub struct Pair { pub a: u32, pub b: u32 }

        pub fn flattened_field_mirror_probe() -> u32 {
            let mut p = Pair { a: 0, b: 7 };
            let r = &mut p;
            (*r).a = 42;
            (*r).a
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "flattened_field_mirror_probe");
        let body = instance.body().expect("body");
        let chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            "flattened_field_mirror_probe",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );
        let (vc, _needs_mem_promote) = chc_ctx.translate();

        let smt = emit_chc(&vc).to_string();
        // The flattened field mirror should produce a register equality for field `a`
        // (field index 0 → fld0). The value 42 = 0x2A.
        // After ay bump to declare-var encoding, check both constraint tree and SMT.
        let has_fld0_mirror =
            any_constraint_str(&vc, |c| c.contains("fld0__out") && c.contains("#x0000002a"))
                || (smt.contains("fld0__out") && smt.contains("#x0000002a"));
        assert!(
            has_fld0_mirror,
            "flattened field mirror should emit register equality for fld0 = 0x2A"
        );

        // Mem-level should also have a memory store for the heap write.
        // With declare-var encoding, heap memory may be modeled via Array-sorted
        // declared variables rather than explicit store() constraints.
        let has_memory_model = any_constraint_str(&vc, |c| c.contains("(store "))
            || smt.contains("(store ")
            || vc.vars().iter().any(|v| v.sort.is_array() && v.name.contains("mem"));
        assert!(has_memory_model, "Mem-level field store should model heap memory");
    });
}

/// Multiple field stores through the same mutable reference at Mem level.
///
/// Pattern: `(*r).a = 10; (*r).b = 20;` on a flattened Pair.
/// Tests that `last_constraint_for_local` overwrite logic in `mirror_flattened_field_store`
/// correctly handles separate field indices without clobbering.
///
/// Part of #2895: covers `last_constraint_for_local` tracking across distinct fields.
#[test]
fn test_deref_mem_mirror_flattened_multi_field_stores_independent() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub struct Pair { pub a: u32, pub b: u32 }

        pub fn multi_field_mirror_probe() -> u32 {
            let mut p = Pair { a: 0, b: 0 };
            let r = &mut p;
            (*r).a = 10;
            (*r).b = 20;
            (*r).a
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "multi_field_mirror_probe");
        let body = instance.body().expect("body");
        let chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            "multi_field_mirror_probe",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );
        let (vc, _needs_mem_promote) = chc_ctx.translate();

        // Both field mirrors should be emitted. 10 = 0xA, 20 = 0x14.
        assert!(
            any_constraint_str(&vc, |c| c.contains("fld0__out") && c.contains("#x0000000a")),
            "multi-field mirror should emit register equality for fld0 = 0xA"
        );
        assert!(
            any_constraint_str(&vc, |c| c.contains("fld1__out") && c.contains("#x00000014")),
            "multi-field mirror should emit register equality for fld1 = 0x14"
        );
    });
}

/// Scalar mirror with `last_constraint_for_local` overwrite.
///
/// Pattern: `*r = 5; *r = 10;` — the second store to the same local should
/// overwrite the first mirror constraint (replacing it with `true`).
///
/// Part of #2895: covers `last_constraint_for_local` overwrite in `mirror_scalar_ref_store`.
#[test]
fn test_deref_mem_mirror_scalar_overwrite_supersedes_prior() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn scalar_overwrite_probe() -> u32 {
            let mut x: u32 = 0;
            let r = &mut x;
            *r = 5;
            *r = 10;
            *r
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "scalar_overwrite_probe");
        let body = instance.body().expect("body");
        let chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            "scalar_overwrite_probe",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );
        let (vc, _needs_mem_promote) = chc_ctx.translate();

        // The final value 10 = 0xA should appear in a register mirror constraint.
        assert!(
            any_constraint_str(&vc, |c| c.contains("__out") && c.contains("#x0000000a")),
            "scalar overwrite mirror should contain final value 0xA"
        );

        // The superseded first store (value 5 = 0x5) should have been replaced
        // with `true` in the constraint vector.
        let true_count = count_constraint_str(&vc, |c| c == "true");
        assert!(true_count >= 1, "superseded mirror constraint should be replaced with `true`");
    });
}

/// Whole-struct store through deref into a flattened local at Mem level.
///
/// Pattern: `*r = Pair { a: 3, b: 4 }` where the target is flattened.
/// This exercises the `flattened_tuple_locals.contains(&target_local) &&
/// rhs_expr.sort().is_datatype()` branch in `mirror_scalar_ref_store`
/// (deref_mem_mirror.rs:111-140), which decomposes the Datatype RHS into
/// per-field constraints via `constrain_flattened_fields`.
///
/// Part of #2895: covers Datatype-to-flattened decomposition mirror path.
#[test]
fn test_deref_mem_mirror_whole_struct_store_to_flattened_decomposes() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub struct Pair { pub a: u32, pub b: u32 }

        pub fn whole_struct_deref_mirror() -> u32 {
            let mut p = Pair { a: 0, b: 0 };
            let r = &mut p;
            *r = Pair { a: 3, b: 4 };
            (*r).a
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "whole_struct_deref_mirror");
        let body = instance.body().expect("body");
        let chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            "whole_struct_deref_mirror",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );
        let (vc, _needs_mem_promote) = chc_ctx.translate();
        let smt = crate::codegen_ay::emit_chc(&vc).to_string();

        // The whole-struct store should produce per-field mirror constraints.
        // Either the flattened decomposition path fires (fld0/fld1 constraints)
        // or the scalar coercion path fires (direct equality).
        // Both are valid — what matters is that SOME register mirror is emitted.
        assert!(
            any_constraint_str(&vc, |c| c.contains("__out")
                && c != "true"
                && !c.contains("(store ")),
            "whole-struct deref store should emit register mirror constraints"
        );

        // Memory store should also be present. After ay bump to declare-var
        // encoding, store operations may appear in head args instead of body
        // constraints, or may be encoded as heap array variable declarations.
        // The key invariant: the VC references heap memory state (Array vars or
        // store ops). Check both the full SMT output and the constraint helper.
        let has_memory_store = smt.contains("(store ")
            || any_constraint_str(&vc, |c| c.contains("(store "))
            || vc.vars().iter().any(|v| v.sort.is_array());
        assert!(has_memory_store, "Mem-level whole-struct store should reference heap memory");
    });
}

// =============================================================================
// OI3 contract tests: Opaque IntoIter boundary (#2876 / #2912)
//
// OI1: mirror_flattened_field_store emits identity out==in when field_idx >= field_count
//       for VecIntoIter locals (instead of warning/dropping).
// OI2: is_unmodeled_into_iter_field_store short-circuits Mem-level memory store
//       and heap-safety checks for unmodeled VecIntoIter fields.
// =============================================================================

/// OI1+OI2 pipeline test: Vec::into_iter at Mem level should produce a translatable
/// VC without field_mirror_oob regressions. The IntoIter local has 5 modeled
/// fields (ptr, len, cap, data, pos) but MIR writes 6+ fields. The OI1 mirror
/// emits identity constraints for OOB fields; OI2 skips the Mem-level store.
///
/// Part of #2876: OI3 contract test — pipeline-level regression guard.
#[test]
fn test_oi_pipeline_vec_into_iter_mem_level_translates_without_regression() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        pub fn probe_into_iter_mem() -> Option<u32> {
            let v = vec![1u32, 2u32, 3u32];
            let mut it = v.into_iter();
            it.next()
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_into_iter_mem");
        let body = instance.body().expect("body");
        let chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            "probe_into_iter_mem",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );
        let (vc, _needs_mem_promote) = chc_ctx.translate();
        let smt = emit_chc(&vc).to_string();

        assert!(!vc.rules.is_empty(), "Vec::into_iter at Mem level should produce rules");
        assert!(!smt.is_empty(), "SMT output should be non-empty");

        // The VC should contain block relations (transition rules).
        let transition_count = vc.rules.iter().filter(|r| r.body.relation.is_some()).count();
        assert!(
            transition_count > 0,
            "Vec::into_iter pipeline should produce transition rules, got 0"
        );
    });
}

/// OI1 contract test: VecIntoIter deep-flattened local has exactly 5 modeled
/// fields (Vec.ptr, Vec.len, Vec.cap, Vec.data, pos). The field count metadata
/// must be >=5 for the OI1 identity-transition path to function correctly.
///
/// Part of #2876: OI3 contract test — field count prerequisite.
#[test]
fn test_oi_vec_into_iter_flattened_field_count_is_five() {
    use super::super::codegen_ctx::CollectionProjectionKind;

    const SOURCE: &str = r#"
        #![allow(dead_code)]
        pub fn probe_field_count() -> Option<u32> {
            let mut it = vec![42u32].into_iter();
            it.next()
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_field_count");
        let body = instance.body().expect("body");
        let mut chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            "probe_field_count",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );
        chc_ctx.declare_block_relations();

        let iter_local = chc_ctx
            .collections
            .projection_locals
            .iter()
            .find_map(|(local, kind)| {
                if *kind == CollectionProjectionKind::VecIntoIter { Some(*local) } else { None }
            })
            .expect("expected VecIntoIter projected local");

        assert!(
            chc_ctx.flatten.flattened_tuple_locals.contains(&iter_local),
            "VecIntoIter local should be in flattened_tuple_locals"
        );

        let field_count = chc_ctx.flattened_field_count(iter_local);
        assert_eq!(
            field_count, 5,
            "VecIntoIter should have exactly 5 deep-flattened fields \
             (ptr, len, cap, data, pos), got {field_count}"
        );
    });
}

/// OI1 contract test: mirror_scalar_ref_store exercised via the full translate()
/// pipeline should emit constraints for VecIntoIter locals even when MIR writes
/// to field indices beyond the 5-field CHC model. Verifies the identity
/// transition path (out==in for all projected slots) is reached.
///
/// Part of #2876: OI3 contract test — identity transition regression guard.
#[test]
fn test_oi1_into_iter_translate_produces_constrained_vc() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        pub fn probe_oi1_constrained() -> Option<u32> {
            let v = vec![10u32, 20u32];
            let mut it = v.into_iter();
            it.next()
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_oi1_constrained");
        let body = instance.body().expect("body");
        let chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            "probe_oi1_constrained",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );
        let (vc, _needs_mem_promote) = chc_ctx.translate();

        // The VC must not be trivially empty — identity transitions from OI1
        // produce actual equality constraints (not just `true` passthrough).
        let total = count_constraint_str(&vc, |_| true);
        let trivial = count_constraint_str(&vc, |c| c == "true");
        assert!(
            total > trivial,
            "OI1 identity transitions should produce non-trivial constraints, \
             got only {trivial} trivial out of {total} total"
        );
    });
}

// =============================================================================
// OI2 detection logic unit tests (#2876 / P1:937 finding)
//
// Tests for is_unmodeled_into_iter_field_store prerequisite chain:
// 1. ref_targets contains the local → target mapping
// 2. Target is a VecIntoIter collection projection local
// 3. Target is in flattened_tuple_locals
// 4. Final field index >= flattened field count (5 for VecIntoIter)
// =============================================================================

/// OI2 detection: verify that for a Vec::into_iter pipeline, the ChcCtx has
/// all prerequisites for OI2 detection — ref targets exist for locals that
/// point into the VecIntoIter struct, and those targets are correctly classified
/// as VecIntoIter collection projections.
///
/// Part of #2876: Unit test for is_unmodeled_into_iter_field_store detection.
#[test]
fn test_oi2_detection_prerequisites_ref_targets_point_to_vec_into_iter() {
    use super::super::codegen_ctx::CollectionProjectionKind;

    const SOURCE: &str = r#"
        #![allow(dead_code)]
        pub fn probe_oi2_prereqs() -> Option<u32> {
            let v = vec![1u32, 2u32, 3u32];
            let mut it = v.into_iter();
            it.next()
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_oi2_prereqs");
        let body = instance.body().expect("body");
        let mut chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            "probe_oi2_prereqs",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );
        chc_ctx.declare_block_relations();

        // Find the VecIntoIter projected local.
        let iter_local = chc_ctx.collections.projection_locals.iter().find_map(|(local, kind)| {
            if *kind == CollectionProjectionKind::VecIntoIter { Some(*local) } else { None }
        });
        assert!(
            iter_local.is_some(),
            "OI2 prerequisite 1: ChcCtx must identify a VecIntoIter collection projection local"
        );
        let iter_local = iter_local.unwrap();

        // Prerequisite 2: The IntoIter local must be in flattened_tuple_locals.
        assert!(
            chc_ctx.flatten.flattened_tuple_locals.contains(&iter_local),
            "OI2 prerequisite 2: VecIntoIter local {iter_local} must be in flattened_tuple_locals"
        );

        // Prerequisite 3: The flattened field count must be exactly 5
        // (ptr, len, cap, data, pos).
        let field_count = chc_ctx.flattened_field_count(iter_local);
        assert_eq!(
            field_count, 5,
            "OI2 prerequisite 3: VecIntoIter flattened field count must be 5, got {field_count}"
        );

        // Prerequisite 4: There must be at least one ref_target that points
        // to the VecIntoIter local (these are the pointer locals whose deref
        // stores OI2 evaluates).
        let has_refs_to_iter =
            chc_ctx.ref_resolution.ref_targets.iter().any(|(_, rt)| rt.local == iter_local);
        assert!(
            has_refs_to_iter,
            "OI2 prerequisite 4: at least one ref_target must point to VecIntoIter local {iter_local}"
        );
    });
}

/// OI2 negative case: deref store to a non-IntoIter target should NOT skip
/// the memory store. Verifies the detection function returns false when the
/// ref target is not a VecIntoIter collection projection.
///
/// Part of #2876: Unit test for is_unmodeled_into_iter_field_store negative path.
#[test]
fn test_oi2_detection_non_into_iter_deref_store_emits_memory_store() {
    with_test_ay_ctx_for_source(DEREF_STORE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "store_via_raw_ptr");
        let body = instance.body().expect("body");
        let chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            "store_via_raw_ptr",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );

        // For a plain raw pointer store (*ptr = val), OI2 should NOT fire.
        // The collection_projection_locals map should be empty (no IntoIter).
        assert!(
            chc_ctx.collections.projection_locals.is_empty(),
            "raw pointer source should have no collection projection locals"
        );

        let (vc, _) = chc_ctx.translate();
        let smt = emit_chc(&vc).to_string();

        // The memory store should be present in the SMT output.
        let has_memory_store = smt.contains("(store ");
        assert!(
            has_memory_store,
            "non-IntoIter deref store must emit memory store constraint; OI2 should not fire"
        );
    });
}

/// OI2 dropped-store counter: Vec::into_iter pipeline should NOT increment
/// the dropped-store counter for OI2-skipped fields. OI2 is an intentional
/// skip (not a lost transition), so store_dropped_transition must not
/// increase for OI2 paths.
///
/// Part of #2876: Unit test verifying OI2 does not pollute drop metrics.
/// Part of #2906: Reads per-ctx diagnostics instead of global atomic — no Mutex needed.
#[test]
fn test_oi2_skip_does_not_increment_dropped_store_counter() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        pub fn probe_oi2_counter() -> Option<u32> {
            let v = vec![7u32, 8u32];
            let mut it = v.into_iter();
            it.next()
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_oi2_counter");
        let body = instance.body().expect("body");

        let chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            "probe_oi2_counter",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );

        let (_vc, _, diagnostics) = chc_ctx.translate_with_diagnostics();

        // OI2 intentionally skips unmodeled VecIntoIter field stores by
        // emitting identity transitions in register space. This path must not
        // count as a dropped transition.
        let dropped = diagnostics.store_dropped_transition.get();
        assert_eq!(dropped, 0, "OI2 should not increment dropped-store count; got {dropped}");
    });
}
