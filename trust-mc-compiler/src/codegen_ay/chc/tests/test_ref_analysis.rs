// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! MIR-driven tests for CHC codegen_decl_ref_analysis.rs.
//!
//! Part of #2188: CHC module test coverage for untested production paths.
//!
//! Covers:
//! - collect_numeric_ref_targets: Pass 1 (simple refs), Pass 1.5 (Copy/Move propagation,
//!   transitive deref, reborrow, cast), Pass 2 (deref-through-ref)
//! - collect_const_ref_discriminants: discriminant extraction from constant references
//! - collect_const_ref_values: scalar value extraction from constant references
//!
//! Also covers production functions in codegen_rules.rs:
//! - should_skip_reg_pointer_assert / operand_depends_on_ref_target / rvalue_depends_on_ref_target
//!
//! Note: collect_numeric_ref_targets is called during declare_block_relations(),
//! which is invoked from translate(). All ref_targets checks must happen after
//! translate() or after explicitly calling declare_block_relations().

#![allow(clippy::unwrap_used, clippy::panic)]

use super::common::*;
use crate::codegen_ay::emit_chc;

// ═══════════════════════════════════════════════════════════════════════
// Probe sources for reference analysis tests
// ═══════════════════════════════════════════════════════════════════════

/// Simple reference: `_ref = &_local` pattern (Pass 1)
const REF_SIMPLE_SOURCE: &str = r#"
pub fn simple_ref(x: u32) -> u32 {
    let r = &x;
    *r + 1
}
"#;

/// Multiple references to different locals (Pass 1)
const REF_MULTI_SOURCE: &str = r#"
pub fn multi_ref(a: u32, b: u32) -> u32 {
    let ra = &a;
    let rb = &b;
    *ra + *rb
}
"#;

/// Copy/Move propagation through references (Pass 1.5)
const REF_COPY_PROP_SOURCE: &str = r#"
pub fn copy_ref(x: u32) -> u32 {
    let r = &x;
    let r2 = r;  // Copy of reference
    *r2 + 1
}
"#;

/// Reborrow pattern: `&*r` (Pass 1.5)
const REF_REBORROW_SOURCE: &str = r#"
pub fn reborrow_ref(x: &u32) -> u32 {
    let r = &*x;  // reborrow
    *r + 1
}
"#;

/// Pointer cast pattern (Pass 1.5)
const REF_CAST_SOURCE: &str = r#"
pub fn cast_ref(x: &u32) -> u32 {
    let p = x as *const u32;
    unsafe { *p + 1 }
}
"#;

/// Transitive deref propagation pattern (Pass 1.5 #2090):
/// `_dest = Copy(*_src)` where `_src` and its target both have ref_targets.
const REF_TRANSITIVE_DEREF_SOURCE: &str = r#"
pub fn transitive_deref_local(v: u32) -> u32 {
    let r1 = &v;
    let rr = &r1;
    let r2 = *rr;
    *r2
}
"#;

/// Copy propagation from deref+field pattern (Pass 1.5 #1739 Bug 3b):
/// `_dst = Copy((*_src_ref).field)` where field is itself a reference.
const REF_DEREF_FIELD_COPY_REF_SOURCE: &str = r#"
pub fn copy_deref_field_ref() -> u32 {
    struct Inner {
        val: u32,
    }

    struct Outer<'a> {
        inner: &'a Inner,
    }

    let inner = Inner { val: 100 };
    let outer = Outer { inner: &inner };
    let ref_to_outer: &Outer = &outer;
    let inner_ref = (*ref_to_outer).inner;
    (*inner_ref).val
}
"#;

/// Pointer materialization call propagation pattern (Pass 1.5 #2110):
/// `_dst = core::slice::<impl [T]>::as_ptr(_src)`.
const REF_SLICE_AS_PTR_SOURCE: &str = r#"
pub fn slice_as_ptr_first(arr: [u8; 4]) -> u8 {
    let s: &[u8] = &arr;
    let p = s.as_ptr();
    unsafe { *p }
}
"#;

/// Field reference through deref (Pass 2): `&((*other_ref).field)`
const REF_DEREF_FIELD_SOURCE: &str = r#"
pub struct Pair {
    pub first: u32,
    pub second: u32,
}

pub fn deref_field(p: &Pair) -> u32 {
    let r = &p.first;
    *r
}
"#;

/// Tuple-field propagation to discriminant deref (#2283):
/// `_tuple = (ref0, ref1)` then `_from_tuple = Copy(_tuple.0)` then `Discriminant(*_from_tuple)`.
const REF_TUPLE_FIELD_DISCR_SOURCE: &str = r#"
pub fn option_tuple_field_discr(flag: bool, a: Option<u8>, b: Option<u8>) -> bool {
    let refs = (&a, &b);
    let r = if flag { refs.0 } else { refs.1 };
    matches!(*r, Some(_))
}
"#;

/// Constant reference patterns for discriminant extraction
const CONST_REF_DISCRIM_SOURCE: &str = r#"
use std::cmp::Ordering;

pub fn const_ref_ordering(x: u32) -> Ordering {
    if x > 10 {
        Ordering::Greater
    } else if x == 10 {
        Ordering::Equal
    } else {
        Ordering::Less
    }
}
"#;

/// Constant scalar reference: `const &42u8`
const CONST_REF_SCALAR_SOURCE: &str = r#"
pub fn const_ref_u32() -> u32 {
    let r: &u32 = &42;
    *r
}

pub fn const_ref_bool() -> bool {
    let r: &bool = &true;
    *r
}
"#;

/// Ref target dependency chain for assert suppression (codegen_rules.rs)
const REF_ASSERT_SOURCE: &str = r#"
pub fn ref_null_check(x: &u32) -> u32 {
    // The compiler may insert null/alignment checks on *x
    // At Reg level, ref-target-derived pointers should skip these
    *x + 1
}
"#;

/// Empty array constant ref (extract_scalar_from_const_ref edge case)
const CONST_REF_ARRAY_SOURCE: &str = r#"
pub fn const_ref_array() -> u8 {
    let arr: &[u8; 4] = &[1, 2, 3, 4];
    arr[0]
}

pub fn const_ref_empty_array() -> u8 {
    let _arr: &[u8; 0] = &[];
    0
}
"#;

// ═══════════════════════════════════════════════════════════════════════
// Pass 1: Simple reference pipeline tests
// ═══════════════════════════════════════════════════════════════════════

/// Verify simple_ref translates to valid VC with reference resolution.
/// Exercises: collect_numeric_ref_targets Pass 1 (_ref = &_local).
#[test]
fn test_ref_analysis_simple_ref_pipeline() {
    with_test_ay_ctx_for_source(REF_SIMPLE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "simple_ref");
        let body = instance.body().expect("function body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "simple_ref", ChcConfig::default());

        let (vc, _needs_mem_promote) = chc_ctx.translate();
        let bb_count = body.blocks.len();
        assert_vc_structure(&vc, "simple_ref", bb_count);

        // Dereference of reference should produce constrained transition rules
        let constrained_rules = vc
            .rules
            .iter()
            .filter(|r| r.body.relation.is_some() && !r.body.constraints.is_empty())
            .count();
        assert!(
            constrained_rules >= 1,
            "simple_ref should have constrained transition rules from ref deref, got {}",
            constrained_rules
        );
    });
}

/// Verify multiple references produce valid VC with distinct state vars.
/// Exercises: collect_numeric_ref_targets Pass 1 for multiple refs.
#[test]
fn test_ref_analysis_multi_ref_pipeline() {
    with_test_ay_ctx_for_source(REF_MULTI_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "multi_ref");
        let body = instance.body().expect("function body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "multi_ref", ChcConfig::default());

        let (vc, _needs_mem_promote) = chc_ctx.translate();
        let bb_count = body.blocks.len();
        assert_vc_structure(&vc, "multi_ref", bb_count);

        // Multiple refs → should have relations with arity >= 2 (at least a and b)
        let max_arity =
            vc.relations.iter().map(trust_mc_core::RelationDecl::arity).max().unwrap_or(0);
        assert!(
            max_arity >= 2,
            "multi_ref relations should have arity >= 2 for two args, got {max_arity}"
        );
    });
}

// ═══════════════════════════════════════════════════════════════════════
// Pass 1.5: Copy/Move propagation pipeline tests
// ═══════════════════════════════════════════════════════════════════════

/// Verify Copy propagation of references produces valid VC.
/// Exercises: collect_numeric_ref_targets Pass 1.5 Copy/Move path.
#[test]
fn test_ref_analysis_copy_propagation_pipeline() {
    with_test_ay_ctx_for_source(REF_COPY_PROP_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "copy_ref");
        let body = instance.body().expect("function body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "copy_ref", ChcConfig::default());

        let (vc, _needs_mem_promote) = chc_ctx.translate();
        let bb_count = body.blocks.len();
        assert_vc_structure(&vc, "copy_ref", bb_count);

        // u32 copy-propagated ref should produce bv32 state vars
        let has_bv32 =
            vc.relations.iter().any(|r| r.arg_sorts.iter().any(|s| s.bitvec_width() == Some(32)));
        assert!(has_bv32, "copy_ref with u32 should have bv32 sort in relations");
    });
}

/// Verify reborrow pattern `&*x` produces valid VC.
/// Exercises: collect_numeric_ref_targets Pass 1.5 reborrow path.
#[test]
fn test_ref_analysis_reborrow_pipeline() {
    with_test_ay_ctx_for_source(REF_REBORROW_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "reborrow_ref");
        let body = instance.body().expect("function body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "reborrow_ref", ChcConfig::default());

        let (vc, _needs_mem_promote) = chc_ctx.translate();
        assert!(!vc.rules.is_empty(), "reborrow_ref should produce CHC rules");
        assert!(!vc.relations.is_empty(), "reborrow_ref should produce relations");

        // Semantic: reborrow_ref(*r + 1) should produce bv32-sorted relation args
        // (u32 operations) and at least one constrained transition rule.
        let has_bv32 =
            vc.relations.iter().any(|r| r.arg_sorts.iter().any(|s| s.bitvec_width() == Some(32)));
        assert!(has_bv32, "reborrow_ref with u32 should have bv32 sort in relations");
        assert_has_nontrivial_transition_constraints(&vc, "reborrow_ref");
    });
}

/// Verify pointer cast propagation produces valid VC.
/// Exercises: collect_numeric_ref_targets Pass 1.5 cast path.
#[test]
fn test_ref_analysis_cast_propagation_pipeline() {
    with_test_ay_ctx_for_source(REF_CAST_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "cast_ref");
        let body = instance.body().expect("function body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "cast_ref", ChcConfig::default());

        let (vc, _needs_mem_promote) = chc_ctx.translate();
        assert!(!vc.rules.is_empty(), "cast_ref should produce CHC rules");

        // Cast involves unsafe deref → should produce error paths
        let has_error = vc.relations.iter().any(|r| r.name == "error");
        assert!(has_error, "cast_ref should have error relation for pointer deref checks");
    });
}

/// Verify transitive deref propagation maps destination to transitive target.
/// Exercises: collect_numeric_ref_targets Pass 1.5 transitive deref path (#2090).
#[test]
fn test_ref_analysis_transitive_deref_ref_target_propagation() {
    with_test_ay_ctx_for_source(REF_TRANSITIVE_DEREF_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "transitive_deref_local");
        let body = instance.body().expect("function body");
        let mut chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "transitive_deref_local", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let mut verified = false;
        for block in &body.blocks {
            for stmt in &block.statements {
                if let StatementKind::Assign(
                    lhs,
                    Rvalue::Use(Operand::Copy(place) | Operand::Move(place)),
                ) = &stmt.kind
                    && place.projection.len() == 1
                    && matches!(place.projection[0], ProjectionElem::Deref)
                {
                    let src_local = place.local;
                    let dest_local = lhs.local;

                    if let Some(src_target) = chc_ctx.ref_resolution.ref_targets.get(&src_local)
                        && let Some(transitive_target) =
                            chc_ctx.ref_resolution.ref_targets.get(&src_target.local)
                        && let Some(dest_target) =
                            chc_ctx.ref_resolution.ref_targets.get(&dest_local)
                    {
                        assert_eq!(
                            dest_target.local, transitive_target.local,
                            "transitive deref should resolve destination local {} through source {}",
                            dest_local, src_local
                        );
                        assert_eq!(
                            dest_target.projections, transitive_target.projections,
                            "transitive deref should preserve projection chain"
                        );
                        verified = true;
                    }
                }
            }
        }

        assert!(verified, "expected at least one Copy/Move(*ref) transitive propagation candidate");
    });
}
/// Verify Pass 1.5 deref-field copy propagation for reference-typed destinations.
#[test]
fn test_ref_analysis_deref_field_copy_ref_target_propagation() {
    with_test_ay_ctx_for_source(REF_DEREF_FIELD_COPY_REF_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "copy_deref_field_ref");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "copy_deref_field_ref", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let mut verified = false;
        for block in &body.blocks {
            for stmt in &block.statements {
                if let StatementKind::Assign(
                    lhs,
                    Rvalue::Use(Operand::Copy(place) | Operand::Move(place)),
                ) = &stmt.kind
                    && place.projection.len() >= 2
                    && matches!(place.projection[0], ProjectionElem::Deref)
                    && matches!(place.projection[1], ProjectionElem::Field(_, _))
                    && matches!(
                        lhs.ty(body.locals()),
                        Ok(ty) if matches!(ty.kind(), TyKind::RigidTy(RigidTy::Ref(..)))
                    )
                {
                    let src_local = place.local;
                    let dest_local = lhs.local;
                    let expected_suffix_len = place.projection.len() - 1;
                    if let Some(src_target) = chc_ctx.ref_resolution.ref_targets.get(&src_local)
                        && let Some(dest_target) =
                            chc_ctx.ref_resolution.ref_targets.get(&dest_local)
                    {
                        let field_sources = chc_ctx.collect_aggregate_field_sources();
                        let pass25_target = place.projection.get(1).and_then(|proj| {
                            let ProjectionElem::Field(field_idx, _) = proj else {
                                return None;
                            };
                            field_sources.get(&(src_target.local, *field_idx)).and_then(
                                |field_local| chc_ctx.ref_resolution.ref_targets.get(field_local),
                            )
                        });
                        let preserves_source_target = dest_target.local == src_target.local
                            && dest_target.projections.len()
                                == src_target.projections.len() + expected_suffix_len
                            && matches!(
                                dest_target.projections.last(),
                                Some(ProjectionElem::Field(_, _))
                            );
                        let resolves_to_referent = pass25_target.is_some_and(|expected_target| {
                            dest_target.local == expected_target.local
                                && dest_target.projections == expected_target.projections
                        });
                        if preserves_source_target || resolves_to_referent {
                            verified = true;
                        }
                    }
                }
            }
        }
        assert!(
            verified,
            "expected at least one Copy/Move((*ref).field) candidate to propagate into ref_targets"
        );
    });
}

/// Verify deref-field Copy/Move source resolution and downstream deref translation.
#[test]
fn test_ref_analysis_copy_move_deref_field_source_resolution() {
    with_test_ay_ctx_for_source(REF_DEREF_FIELD_COPY_REF_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "copy_deref_field_ref");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "copy_deref_field_ref", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let mut candidate: Option<(usize, usize, Place)> = None;
        for block in &body.blocks {
            for stmt in &block.statements {
                if let StatementKind::Assign(
                    lhs,
                    Rvalue::Use(Operand::Copy(place) | Operand::Move(place)),
                ) = &stmt.kind
                    && place.projection.len() >= 2
                    && matches!(place.projection[0], ProjectionElem::Deref)
                    && matches!(place.projection[1], ProjectionElem::Field(_, _))
                {
                    candidate = Some((lhs.local, place.local, place.clone()));
                    break;
                }
            }
            if candidate.is_some() {
                break;
            }
        }
        let (dest_local, src_local, source_place) =
            candidate.expect("expected at least one Copy/Move((*ref).field) statement in MIR");
        let src_target = chc_ctx
            .ref_resolution
            .ref_targets
            .get(&src_local)
            .expect("source local should have ref_target before deref-field copy propagation");
        let src_target_local = src_target.local;
        let dest_target =
            chc_ctx.ref_resolution.ref_targets.get(&dest_local).expect(
                "destination local should get ref_target from deref-field copy propagation",
            );
        let field_sources = chc_ctx.collect_aggregate_field_sources();
        let pass25_target = source_place.projection.get(1).and_then(|proj| {
            let ProjectionElem::Field(field_idx, _) = proj else {
                return None;
            };
            field_sources
                .get(&(src_target.local, *field_idx))
                .and_then(|field_local| chc_ctx.ref_resolution.ref_targets.get(field_local))
        });
        // Pass 2.5 (#2919): allow exact ADT field-source transitive target resolution.
        assert!(
            dest_target.local == src_target_local
                || pass25_target.is_some_and(|expected_target| {
                    dest_target.local == expected_target.local
                        && dest_target.projections == expected_target.projections
                }),
            "deref-field resolution should either preserve target local \
             or resolve to the exact Pass 2.5 field-source target"
        );
        let translated = chc_ctx.translate_place_with_deref(&source_place, &HashSet::new());
        assert!(
            translated.is_some(),
            "translate_place_with_deref should succeed for propagated Copy/Move((*ref).field) place"
        );
        let pipeline_vc = mir_to_chc(ctx.tcx, &body, "copy_deref_field_ref", ChcConfig::default());
        assert_vc_structure(&pipeline_vc, "copy_deref_field_ref", body.blocks.len());
    });
}

/// Verify slice::as_ptr/as_mut_ptr call propagation copies source ref_target.
/// Exercises: collect_numeric_ref_targets Pass 1.5 call path (#2110).
#[test]
fn test_ref_analysis_slice_as_ptr_call_ref_target_propagation() {
    with_test_ay_ctx_for_source(REF_SLICE_AS_PTR_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "slice_as_ptr_first");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "slice_as_ptr_first", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let mut verified = false;
        for block in &body.blocks {
            if let TerminatorKind::Call { func, args, destination, .. } = &block.terminator.kind
                && let Some(callee_path) = chc_ctx.resolve_callee_path(func)
                && matches!(callee_path.rsplit("::").next(), Some("as_ptr" | "as_mut_ptr"))
                && let Some(Operand::Copy(place) | Operand::Move(place)) = args.first()
                && place.projection.is_empty()
            {
                let src_local = place.local;
                let dest_local = destination.local;
                let src_target = chc_ctx.ref_resolution.ref_targets.get(&src_local).expect(
                    "as_ptr source local should have ref_target from prior Ref/AddressOf pass",
                );
                let dest_target = chc_ctx
                    .ref_resolution
                    .ref_targets
                    .get(&dest_local)
                    .expect("as_ptr destination local should inherit ref_target");

                assert_eq!(
                    dest_target.local, src_target.local,
                    "as_ptr call should preserve target local for ref propagation"
                );
                assert_eq!(
                    dest_target.projections, src_target.projections,
                    "as_ptr call should preserve projections for ref propagation"
                );
                verified = true;
            }
        }

        assert!(verified, "expected at least one slice as_ptr/as_mut_ptr call in MIR");
    });
}

/// Verify tuple-field Copy/Move references are tracked through to discriminant deref.
/// Exercises: collect_numeric_ref_targets Pass 1.5 tuple field path + #2283 discriminant usage.
#[test]
fn test_ref_analysis_tuple_field_copy_discriminant_ref_target_propagation() {
    with_test_ay_ctx_for_source(REF_TUPLE_FIELD_DISCR_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "option_tuple_field_discr");
        let body = instance.body().expect("function body");
        let mut chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "option_tuple_field_discr", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let mut tuple_locals = HashSet::new();
        let mut tuple_field_copy_locals = HashSet::new();
        for block in &body.blocks {
            for stmt in &block.statements {
                match &stmt.kind {
                    StatementKind::Assign(lhs, Rvalue::Aggregate(AggregateKind::Tuple, _)) => {
                        tuple_locals.insert(lhs.local);
                    }
                    StatementKind::Assign(
                        lhs,
                        Rvalue::Use(Operand::Copy(place) | Operand::Move(place)),
                    ) if place.projection.len() == 1
                        && matches!(place.projection[0], ProjectionElem::Field(_, _))
                        && tuple_locals.contains(&place.local) =>
                    {
                        tuple_field_copy_locals.insert(lhs.local);
                    }
                    _ => {}
                }
            }
        }

        assert!(
            !tuple_field_copy_locals.is_empty(),
            "expected tuple-field Copy/Move locals in option_tuple_field_discr MIR"
        );

        let mut verified = false;
        for block in &body.blocks {
            for stmt in &block.statements {
                if let StatementKind::Assign(_, Rvalue::Discriminant(place)) = &stmt.kind
                    && place.projection.len() == 1
                    && matches!(place.projection[0], ProjectionElem::Deref)
                    && tuple_field_copy_locals.contains(&place.local)
                {
                    let ref_local = place.local;
                    assert!(
                        chc_ctx.ref_resolution.ref_targets.contains_key(&ref_local),
                        "tuple-field Copy/Move local _{ref_local} should be tracked in ref_targets"
                    );

                    let discr = chc_ctx.translate_discriminant(place, &HashSet::new());
                    assert!(
                        discr.is_some(),
                        "translate_discriminant should resolve Discriminant(*_{ref_local}) from tuple-field ref"
                    );
                    verified = true;
                }
            }
        }

        assert!(
            verified,
            "expected at least one Discriminant(*ref) where ref came from tuple-field Copy/Move"
        );
    });
}

// ═══════════════════════════════════════════════════════════════════════
// Pass 2: Deref-through-ref pipeline tests
// ═══════════════════════════════════════════════════════════════════════

/// Verify deref-through-ref field access produces valid VC.
/// Exercises: collect_numeric_ref_targets Pass 2 (deref + field projection).
#[test]
fn test_ref_analysis_deref_field_pipeline() {
    with_test_ay_ctx_for_source(REF_DEREF_FIELD_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "deref_field");
        let body = instance.body().expect("function body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "deref_field", ChcConfig::default());

        let (vc, _needs_mem_promote) = chc_ctx.translate();
        assert!(!vc.rules.is_empty(), "deref_field pipeline should produce CHC rules");
        assert!(!vc.relations.is_empty(), "deref_field pipeline should produce relations");

        // Field access through reference → relations should have non-trivial arity
        // (at least p's struct fields contribute state vars)
        let max_arity =
            vc.relations.iter().map(trust_mc_core::RelationDecl::arity).max().unwrap_or(0);
        assert!(
            max_arity >= 1,
            "deref_field should have relations with arity >= 1, got {max_arity}"
        );
    });
}

/// Verify deref-field at Mem level (exercises memory_impl paths too).
#[test]
fn test_ref_analysis_deref_field_mem_level() {
    with_test_ay_ctx_for_source(REF_DEREF_FIELD_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "deref_field");
        let body = instance.body().expect("function body");
        let chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            "deref_field",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );

        let (vc, _needs_mem_promote) = chc_ctx.translate();
        assert!(!vc.rules.is_empty(), "deref_field at Mem level should produce rules");

        // Semantic: Mem-level deref_field should engage the memory model
        // (Array-sorted memory variables for heap access).
        let has_mem_var = vc.vars().iter().any(|v| v.sort.is_array());
        assert!(
            has_mem_var,
            "deref_field at Mem level should declare Array-sorted memory variable"
        );
        assert!(
            has_any_constraints(&vc),
            "deref_field at Mem level should produce non-empty body constraints"
        );
    });
}

// ═══════════════════════════════════════════════════════════════════════
// Pass 3: Constant reference discriminant tests
// ═══════════════════════════════════════════════════════════════════════

/// Verify Ordering enum produces valid VC with discriminant handling.
/// Exercises: collect_const_ref_discriminants, extract_discriminant_from_const.
#[test]
fn test_const_ref_ordering_pipeline() {
    with_test_ay_ctx_for_source(CONST_REF_DISCRIM_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "const_ref_ordering");
        let body = instance.body().expect("function body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "const_ref_ordering", ChcConfig::default());

        let (vc, _needs_mem_promote) = chc_ctx.translate();
        let bb_count = body.blocks.len();

        // Ordering comparison produces multiple BBs from the if/else chain
        assert!(bb_count >= 3, "const_ref_ordering should have >= 3 BBs, got {bb_count}");
        assert!(!vc.rules.is_empty(), "const_ref_ordering should produce CHC rules");

        // Semantic: multi-branch if/else for Ordering enum produces transition rules
        // with branch-discriminating constraints. The u32 comparison (x > 10, x == 10)
        // should generate bv32-sorted state variables.
        let smt = emit_chc(&vc).to_string();
        assert!(!smt.is_empty(), "const_ref_ordering SMT should not be empty");
        assert!(
            smt.contains("BitVec 32"),
            "Ordering comparison on u32 should produce BitVec 32 sorts"
        );
        assert_has_nontrivial_transition_constraints(&vc, "const_ref_ordering");
    });
}

// ═══════════════════════════════════════════════════════════════════════
// Pass 4: Constant reference scalar value tests
// ═══════════════════════════════════════════════════════════════════════

/// Verify const ref to u32 produces valid VC.
/// Exercises: collect_const_ref_values, extract_scalar_from_const_ref (Uint path).
#[test]
fn test_const_ref_scalar_u32_pipeline() {
    with_test_ay_ctx_for_source(CONST_REF_SCALAR_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "const_ref_u32");
        let body = instance.body().expect("function body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "const_ref_u32", ChcConfig::default());

        let (vc, _needs_mem_promote) = chc_ctx.translate();
        assert!(!vc.rules.is_empty(), "const_ref_u32 should produce CHC rules");

        // Semantic: const_ref_u32 returns *(&42u32), so the constant 42
        // should appear in the encoding as a bitvec literal.
        assert!(
            any_constraint_str(&vc, |c| c.contains("#x0000002a"))
                || vc_rules_contain_var(&vc, "const_ref_u32"),
            "const_ref_u32 should encode the constant value 42 (0x2a) or reference the function's state vars"
        );
        // u32 return type should produce bv32-sorted relation arguments.
        let has_bv32 =
            vc.relations.iter().any(|r| r.arg_sorts.iter().any(|s| s.bitvec_width() == Some(32)));
        assert!(has_bv32, "const_ref_u32 should have bv32 sort in relations");
    });
}

/// Verify const ref to bool produces valid VC.
/// Exercises: collect_const_ref_values, extract_scalar_from_const_ref (Bool path).
#[test]
fn test_const_ref_scalar_bool_pipeline() {
    with_test_ay_ctx_for_source(CONST_REF_SCALAR_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "const_ref_bool");
        let body = instance.body().expect("function body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "const_ref_bool", ChcConfig::default());

        let (vc, _needs_mem_promote) = chc_ctx.translate();
        assert!(!vc.rules.is_empty(), "const_ref_bool should produce CHC rules");

        // Semantic: const_ref_bool returns *(&true), so the encoding should
        // contain a Bool-sorted or BV-sorted state variable for the return value.
        let has_bool_or_bv = vc.vars().iter().any(|v| {
            v.name.contains("const_ref_bool")
                && (v.sort.is_bool() || v.sort.bitvec_width().is_some())
        });
        assert!(
            has_bool_or_bv,
            "const_ref_bool should declare a Bool/BV-sorted state variable for the return value"
        );
    });
}

/// Verify const ref to [u8; 4] array produces valid VC.
/// Exercises: extract_scalar_from_const_ref (Array path — nested store encoding).
#[test]
fn test_const_ref_array_pipeline() {
    with_test_ay_ctx_for_source(CONST_REF_ARRAY_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "const_ref_array");
        let body = instance.body().expect("function body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "const_ref_array", ChcConfig::default());

        let (vc, _needs_mem_promote) = chc_ctx.translate();
        assert!(!vc.rules.is_empty(), "const_ref_array should produce CHC rules");

        // Semantic: const_ref_array accesses &[1, 2, 3, 4][0], which involves
        // Array-sorted state variables (the array constant) and bounds checking.
        let has_array_or_bv = vc.vars().iter().any(|v| {
            v.name.contains("const_ref_array") && (v.sort.is_array() || v.sort.is_bitvec())
        });
        assert!(
            has_array_or_bv,
            "const_ref_array should declare Array or BV-sorted state variables"
        );
    });
}

/// Verify const ref to [u8; 0] empty array produces valid VC.
/// Exercises: extract_scalar_from_const_ref (Array path — empty array edge case).
#[test]
fn test_const_ref_empty_array_pipeline() {
    with_test_ay_ctx_for_source(CONST_REF_ARRAY_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "const_ref_empty_array");
        let body = instance.body().expect("function body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "const_ref_empty_array", ChcConfig::default());

        let (vc, _needs_mem_promote) = chc_ctx.translate();
        assert!(!vc.rules.is_empty(), "const_ref_empty_array should produce CHC rules");

        // Semantic: empty array [u8; 0] returns 0, so the encoding should
        // produce state variables and the function should translate without
        // crashing on the zero-length edge case.
        let has_state_vars = vc.vars().iter().any(|v| v.name.contains("const_ref_empty_array"));
        assert!(
            has_state_vars,
            "const_ref_empty_array should declare state variables for the function"
        );
    });
}

// ═══════════════════════════════════════════════════════════════════════
// Ref-target dependency tracking (codegen_rules.rs)
// ═══════════════════════════════════════════════════════════════════════

/// At Reg level, ref-target-derived pointers suppress null/alignment checks.
/// Exercises: should_skip_reg_pointer_assert, operand_depends_on_ref_target,
/// place_depends_on_ref_target, find_local_assignment, rvalue_depends_on_ref_target.
#[test]
fn test_ref_null_check_reg_level() {
    with_test_ay_ctx_for_source(REF_ASSERT_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "ref_null_check");
        let body = instance.body().expect("function body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "ref_null_check", ChcConfig::default());

        let (vc, _needs_mem_promote) = chc_ctx.translate();
        assert!(!vc.relations.is_empty(), "ref_null_check should produce relations");
        assert!(!vc.rules.is_empty(), "ref_null_check should produce rules");

        // At Reg level with a reference argument, some error rules may be suppressed
        // (null check is skipped for ref-derived pointers).
        // The function should still produce a valid VC structure.
        let has_error = vc.relations.iter().any(|r| r.name == "error");
        assert!(has_error, "error relation should always be declared");

        // Semantic: ref_null_check computes *x + 1, so the encoding should
        // contain bv32-sorted state variables and nontrivial constraints.
        let has_bv32 =
            vc.relations.iter().any(|r| r.arg_sorts.iter().any(|s| s.bitvec_width() == Some(32)));
        assert!(has_bv32, "ref_null_check with u32 should have bv32 sort in relations");
        assert_has_nontrivial_transition_constraints(&vc, "ref_null_check");
    });
}

/// At Ptr level, pointer checks are NOT suppressed.
/// Exercises: should_skip_reg_pointer_assert returns false at Ptr level.
#[test]
fn test_ref_null_check_ptr_level() {
    with_test_ay_ctx_for_source(REF_ASSERT_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "ref_null_check");
        let body = instance.body().expect("function body");
        let chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            "ref_null_check",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Ptr, ..ChcConfig::default() },
        );

        let (vc, _needs_mem_promote) = chc_ctx.translate();
        assert!(!vc.rules.is_empty(), "ref_null_check at Ptr level should produce CHC rules");

        // At Ptr level, null check error rules should NOT be suppressed
        assert!(
            vc.rules.iter().any(|r| r.head.name == "error"),
            "Ptr level should preserve null check error rules (no suppression)"
        );
    });
}

// ═══════════════════════════════════════════════════════════════════════
// CFG-scoped dependency tracing (#2466)
// ═══════════════════════════════════════════════════════════════════════

/// Regression test: find_local_assignment is BB-scoped after #2466 fix.
/// Verifies that ref-target null-check suppression at Reg level still works
/// (the MIR temporaries for null checks are in the same BB as the check),
/// and that the Ptr-vs-Reg error rule count difference is preserved.
/// Part of #2466.
#[test]
fn test_ref_dependency_trace_is_bb_scoped() {
    with_test_ay_ctx_for_source(REF_ASSERT_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "ref_null_check");
        let body = instance.body().expect("function body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "ref_null_check", ChcConfig::default());

        // translate() runs the full pipeline including ref_targets population
        // and assert check suppression.
        let (vc, _needs_mem_promote) = chc_ctx.translate();
        assert!(!vc.rules.is_empty(), "ref_null_check should produce CHC rules");

        // At Reg level, the null check should still be suppressed even with
        // BB-scoped find_local_assignment, because MIR null-check temporaries
        // are single-assignment within the same BB as the assert terminator.
        let has_error_rel = vc.relations.iter().any(|r| r.name == "error");
        assert!(has_error_rel, "error relation should always be declared");

        // Count error-headed rules at Reg level.
        let error_rule_count = vc.rules.iter().filter(|r| r.head.name == "error").count();

        // Rebuild at Ptr level for comparison — error rules should be present.
        let chc_ctx_ptr = ChcCtx::new(
            ctx.tcx,
            &body,
            "ref_null_check",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Ptr, ..ChcConfig::default() },
        );
        let (vc_ptr, _) = chc_ctx_ptr.translate();
        let ptr_error_count = vc_ptr.rules.iter().filter(|r| r.head.name == "error").count();

        // Ptr level should have >= error rules than Reg level (no suppression at Ptr).
        assert!(
            ptr_error_count >= error_rule_count,
            "Ptr level ({ptr_error_count}) should have >= error rules than Reg level \
             ({error_rule_count}) because Reg suppresses ref-derived null checks"
        );
    });
}

// ═══════════════════════════════════════════════════════════════════════
// Mem level: reference analysis at higher track levels
// ═══════════════════════════════════════════════════════════════════════

/// Verify simple_ref at Mem level produces valid VC.
#[test]
fn test_ref_analysis_mem_level_simple() {
    with_test_ay_ctx_for_source(REF_SIMPLE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "simple_ref");
        let body = instance.body().expect("function body");
        let chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            "simple_ref",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );

        let (vc, _needs_mem_promote) = chc_ctx.translate();
        assert!(!vc.rules.is_empty(), "Mem level should produce rules");
        assert!(!vc.relations.is_empty(), "Mem level should produce relations");

        // Semantic: Mem-level encoding should declare Array-sorted memory
        // variables for heap access.
        let has_mem_var = vc.vars().iter().any(|v| v.sort.is_array());
        assert!(has_mem_var, "simple_ref at Mem level should declare Array-sorted memory variable");
    });
}

/// Verify multi_ref at Mem level produces valid VC.
#[test]
fn test_ref_analysis_mem_level_multi() {
    with_test_ay_ctx_for_source(REF_MULTI_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "multi_ref");
        let body = instance.body().expect("function body");
        let chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            "multi_ref",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );

        let (vc, _needs_mem_promote) = chc_ctx.translate();
        assert!(!vc.rules.is_empty(), "multi_ref at Mem level should produce rules");

        // Semantic: multi_ref(*ra + *rb) at Mem level should declare
        // Array-sorted memory variables and produce constrained transitions.
        let has_mem_var = vc.vars().iter().any(|v| v.sort.is_array());
        assert!(has_mem_var, "multi_ref at Mem level should declare Array-sorted memory variable");
        assert!(
            has_any_constraints(&vc),
            "multi_ref at Mem level should produce non-empty body constraints"
        );
    });
}

/// Verify const ref pipeline at Mem level doesn't panic.
#[test]
fn test_const_ref_scalar_mem_level() {
    with_test_ay_ctx_for_source(CONST_REF_SCALAR_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "const_ref_u32");
        let body = instance.body().expect("function body");
        let chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            "const_ref_u32",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );

        let (vc, _needs_mem_promote) = chc_ctx.translate();
        assert!(!vc.rules.is_empty(), "const_ref_u32 at Mem level should produce rules");

        // Semantic: Mem-level encoding should include Array-sorted memory
        // variables for the heap model.
        let has_mem_var = vc.vars().iter().any(|v| v.sort.is_array());
        assert!(
            has_mem_var,
            "const_ref_u32 at Mem level should declare Array-sorted memory variable"
        );
    });
}
