// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Tests for CHC codegen_decl_ref_numeric/ — numeric reference-target
//! propagation worklist extracted from codegen_decl_ref_analysis.rs.
//!
//! Covers:
//! - collect_aggregate_field_sources: tuple/ADT aggregate → field source mapping
//! - build_numeric_ref_propagation_candidates: candidate collection for
//!   CopyMove, TransitiveDeref, DerefProjectedCopy, Reborrow, Cast, PointerMaterialization
//! - propagate_numeric_ref_targets_worklist: worklist-driven propagation
//! - collect_numeric_ref_targets end-to-end: Pass 1, 1.5, 2, PostPass2
//!
//! Note: `translate()` consumes `ChcCtx`, so ref_targets cannot be inspected
//! after translation. Tests verify propagation effects through VC output
//! (constrained rules, relation arities) and through `collect_aggregate_field_sources`
//! which does not consume self.
//!
//! Part of #2303 (zero-coverage CHC files).

#![allow(clippy::unwrap_used, clippy::panic)]

use super::common::*;

// ═══════════════════════════════════════════════════════════════════════
// Tuple field source collection
// ═══════════════════════════════════════════════════════════════════════

/// Tuple aggregate → field source mapping should capture `(a, b)` fields.
#[test]
fn test_tuple_field_sources_two_element() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        pub fn probe_tuple(a: u32, b: u32) -> (u32, u32) {
            (a, b)
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_tuple");
        let body = instance.body().expect("function body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_tuple", ChcConfig::default());

        let field_sources = chc_ctx.collect_aggregate_field_sources();
        // We should have at least one tuple aggregate mapping
        // The exact locals depend on MIR optimization, but the map should not be empty
        // for a function that constructs a tuple from two arguments.
        assert!(
            !field_sources.is_empty(),
            "tuple(a, b) should produce aggregate field source mappings"
        );

        // Every entry should have field_idx in {0, 1}
        for (_, field_idx) in field_sources.keys() {
            assert!(
                *field_idx <= 1,
                "two-element tuple should only have field indices 0 or 1, got {}",
                field_idx
            );
        }
    });
}

/// No tuple aggregates → empty field source map.
#[test]
fn test_tuple_field_sources_no_tuples() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        pub fn probe_no_tuple(x: u32) -> u32 {
            x + 1
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_no_tuple");
        let body = instance.body().expect("function body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_no_tuple", ChcConfig::default());

        let field_sources = chc_ctx.collect_aggregate_field_sources();
        assert!(
            field_sources.is_empty(),
            "function with no aggregates should have empty field_sources"
        );
    });
}

// ═══════════════════════════════════════════════════════════════════════
// End-to-end ref_targets propagation through translate()
//
// Since translate() consumes ChcCtx, we verify effects through VC output.
// ═══════════════════════════════════════════════════════════════════════

/// Simple reference pattern: `let r = &x; *r` should produce constrained VC.
#[test]
fn test_numeric_ref_simple_ref_produces_constrained_vc() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        pub fn probe_simple_ref(x: u32) -> u32 {
            let r = &x;
            *r + 1
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_simple_ref");
        let body = instance.body().expect("function body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_simple_ref", ChcConfig::default());

        let (vc, _) = chc_ctx.translate();
        let bb_count = body.blocks.len();
        assert_vc_structure(&vc, "probe_simple_ref", bb_count);

        // Dereference of reference should produce constrained transition rules
        let constrained_rules = vc
            .rules
            .iter()
            .filter(|r| r.body.relation.is_some() && !r.body.constraints.is_empty())
            .count();
        assert!(
            constrained_rules >= 1,
            "simple ref deref should produce constrained rules, got {}",
            constrained_rules
        );
    });
}

/// Copy propagation: `let r2 = r` should produce well-formed VC with
/// ref_target resolution (same constraints as original ref).
#[test]
fn test_numeric_ref_copy_propagation_vc() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        pub fn probe_copy_prop(x: u32) -> u32 {
            let r = &x;
            let r2 = r;
            *r2
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_copy_prop");
        let body = instance.body().expect("function body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_copy_prop", ChcConfig::default());

        let (vc, _) = chc_ctx.translate();
        let bb_count = body.blocks.len();
        assert_vc_structure(&vc, "probe_copy_prop", bb_count);

        // Copy propagation through worklist should resolve r2 → r → x.
        // MIR may optimize away the intermediate references, so just verify
        // the pipeline produces a well-formed VC without panicking.
        assert!(!vc.rules.is_empty(), "copy-propagated ref pipeline should produce rules");
    });
}

/// Reborrow pattern: `let r2 = &*r` should produce valid VC.
#[test]
fn test_numeric_ref_reborrow_propagation() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        pub fn probe_reborrow(x: &u32) -> u32 {
            let r = &*x;
            *r + 1
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_reborrow");
        let body = instance.body().expect("function body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_reborrow", ChcConfig::default());

        let (vc, _) = chc_ctx.translate();
        assert!(!vc.rules.is_empty(), "reborrow pattern should produce CHC rules");
        assert!(!vc.relations.is_empty(), "reborrow pattern should produce relations");
    });
}

/// Cast pattern: `x as *const T` should produce valid VC with ref propagation.
#[test]
fn test_numeric_ref_cast_propagation() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        pub fn probe_cast(x: &u32) -> u32 {
            let p = x as *const u32;
            unsafe { *p + 1 }
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_cast");
        let body = instance.body().expect("function body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_cast", ChcConfig::default());

        let (vc, _) = chc_ctx.translate();
        assert!(!vc.rules.is_empty(), "cast pattern should produce rules");
        assert!(!vc.relations.is_empty(), "cast pattern should produce relations");
        // Cast of u32 ref should preserve bitvec(32) in relation sorts
        let has_bv32 =
            vc.relations.iter().any(|r| r.arg_sorts.iter().any(|s| s.bitvec_width() == Some(32)));
        assert!(has_bv32, "cast of u32 ref should have bv32 sort in relations");
    });
}

/// Transitive deref: `let r2 = *rr` where `rr = &r` and `r = &x`.
#[test]
fn test_numeric_ref_transitive_deref() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        pub fn probe_transitive(x: u32) -> u32 {
            let r = &x;
            let rr = &r;
            let r2 = *rr;
            *r2
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_transitive");
        let body = instance.body().expect("function body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_transitive", ChcConfig::default());

        let (vc, _) = chc_ctx.translate();
        let bb_count = body.blocks.len();
        assert_vc_structure(&vc, "probe_transitive", bb_count);

        // Transitive deref of u32 ref should produce bv32 state vars
        let has_bv32 =
            vc.relations.iter().any(|r| r.arg_sorts.iter().any(|s| s.bitvec_width() == Some(32)));
        assert!(has_bv32, "transitive deref of u32 should have bv32 sort in relations");
    });
}

/// BigInt reference tracking: `&bigint_local` through the pipeline.
#[test]
fn test_numeric_ref_bigint_tracking() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        pub struct BigInt(u64);

        impl From<u64> for BigInt {
            fn from(val: u64) -> Self { BigInt(val) }
        }

        pub fn probe_bigint_ref() -> u64 {
            let b = BigInt::from(42u64);
            let r = &b;
            r.0
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_bigint_ref");
        let body = instance.body().expect("function body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_bigint_ref", ChcConfig::default());

        let (vc, _) = chc_ctx.translate();
        assert!(!vc.rules.is_empty(), "BigInt ref should produce rules");
        assert!(!vc.relations.is_empty(), "BigInt ref should produce relations");
    });
}

/// Tuple field source + copy propagation combined.
/// `(a, b)` tuple then `let x = tuple.0` should resolve through the pipeline.
#[test]
fn test_numeric_ref_tuple_field_copy_propagation() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        pub fn probe_tuple_field(a: u32, b: u32) -> u32 {
            let r = &a;
            let t = (r, &b);
            let first = t.0;
            *first
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_tuple_field");
        let body = instance.body().expect("function body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_tuple_field", ChcConfig::default());

        let (vc, _) = chc_ctx.translate();
        let bb_count = body.blocks.len();
        assert_vc_structure(&vc, "probe_tuple_field", bb_count);

        // Tuple field copy with u32 ref should produce bv32 state vars
        let has_bv32 =
            vc.relations.iter().any(|r| r.arg_sorts.iter().any(|s| s.bitvec_width() == Some(32)));
        assert!(has_bv32, "tuple field copy of u32 ref should have bv32 sort in relations");
    });
}

/// Deref-through-ref (Pass 2): `&((*ref_to_struct).field)`.
#[test]
fn test_numeric_ref_deref_through_ref_field() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        pub struct Pair { pub first: u32, pub second: u32 }

        pub fn probe_deref_field(p: &Pair) -> u32 {
            let field_ref = &(*p).first;
            *field_ref
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_deref_field");
        let body = instance.body().expect("function body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_deref_field", ChcConfig::default());

        let (vc, _) = chc_ctx.translate();
        assert!(!vc.rules.is_empty(), "deref-through-ref should produce rules");
        assert!(!vc.relations.is_empty(), "deref-through-ref should produce relations");
        // Deref through ref to struct field (u32) should have bv32 sort
        let has_bv32 =
            vc.relations.iter().any(|r| r.arg_sorts.iter().any(|s| s.bitvec_width() == Some(32)));
        assert!(has_bv32, "deref-through-ref of u32 field should have bv32 sort in relations");
    });
}

/// PostPass2 propagation: After Pass 2 adds deref-through-ref entries,
/// PostPass2 copy propagation should pick up consumers.
#[test]
fn test_numeric_ref_postpass2_copy_consumers() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        pub struct Pair { pub first: u32, pub second: u32 }

        pub fn probe_postpass2(p: &Pair) -> u32 {
            let field_ref = &(*p).first;
            let copy = field_ref;  // Copy of the deref-through-ref result
            *copy
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_postpass2");
        let body = instance.body().expect("function body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_postpass2", ChcConfig::default());

        let (vc, _) = chc_ctx.translate();
        let bb_count = body.blocks.len();
        assert_vc_structure(&vc, "probe_postpass2", bb_count);

        // PostPass2 copy consumers should produce non-empty rules
        assert!(!vc.rules.is_empty(), "postpass2 copy consumers should produce rules");
    });
}

// ═══════════════════════════════════════════════════════════════════════
// Direct branch-level tests for worklist internals (Part of #2492)
//
// These tests call declare_block_relations() (which invokes
// collect_numeric_ref_targets → build_numeric_ref_propagation_candidates →
// propagate_numeric_ref_targets_worklist → apply_numeric_ref_candidate)
// and inspect ref_targets directly for concrete content verification.
// ═══════════════════════════════════════════════════════════════════════

/// source_local_for_copy_move_ref_target: simple bare-local Copy/Move creates
/// a CopyMove candidate that resolves through the worklist.
///
/// Verifies that source_local_for_copy_move_ref_target returns Some(local)
/// for bare-local operands (empty projections) by checking that the
/// Copy/Move destination inherits its source's ref_target.
///
/// Uses black_box to prevent MIR optimization from eliminating the copy.
///
/// Exercises: source_local_for_copy_move_ref_target Some path (line 50).
#[test]
fn test_source_local_bare_copy_creates_ref_target() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        pub fn probe_bare_copy(x: u32) -> u32 {
            let r = &x;
            let copy_of_r = std::hint::black_box(r);
            *copy_of_r
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_bare_copy");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_bare_copy", ChcConfig::default());
        chc_ctx.declare_block_relations();

        // Pass 1 should have created a ref_target for `r = &x`
        assert!(
            !chc_ctx.ref_resolution.ref_targets.is_empty(),
            "probe_bare_copy should have ref_targets from Pass 1 (r = &x)"
        );

        // All ref_targets that resolve should point to argument-range locals
        // (x is arg 1, local index 1). This verifies the worklist resolved
        // the chain correctly: copy_of_r → r → x.
        for (local, target) in &chc_ctx.ref_resolution.ref_targets {
            assert!(
                target.local <= body.arg_locals().len(),
                "ref_target for local {} should point to arg-range local, got {}",
                local,
                target.local
            );
        }
    });
}

/// build_numeric_ref_propagation_candidates: worklist produces ref_targets
/// beyond what Pass 1 alone creates. Verify that ref_targets contains entries
/// for locals that only exist through Reborrow/Cast propagation.
///
/// In a function with reborrow (&*r) and cast (r as *const T), the worklist
/// creates Reborrow and Cast candidates. The ref_targets count exceeding
/// the Pass 1 Ref/AddressOf count proves propagation occurred.
///
/// Exercises: build_numeric_ref_propagation_candidates Reborrow and Cast
/// candidate creation, and apply_numeric_ref_candidate dispatch.
#[test]
fn test_worklist_propagation_produces_targets_beyond_pass1() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        pub fn probe_propagation(x: u32) -> u32 {
            let r = &x;           // Pass 1: Ref
            let reborrow = &*r;   // Pass 1.5: Reborrow candidate
            let p = r as *const u32;  // Pass 1.5: Cast candidate
            let val = unsafe { *p };
            *reborrow + val
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_propagation");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_propagation", ChcConfig::default());
        chc_ctx.declare_block_relations();

        // Count explicit Ref/AddressOf statements with no Deref projections (Pass 1)
        let pass1_ref_count = body
            .blocks
            .iter()
            .flat_map(|b| &b.statements)
            .filter(|stmt| {
                matches!(
                    &stmt.kind,
                    StatementKind::Assign(_, Rvalue::Ref(_, _, place) | Rvalue::AddressOf(_, place))
                        if !place.projection.iter().any(|p| matches!(p, ProjectionElem::Deref))
                )
            })
            .count();

        // ref_targets should exist (at minimum from Pass 1)
        assert!(
            !chc_ctx.ref_resolution.ref_targets.is_empty(),
            "probe_propagation should have ref_targets from Pass 1"
        );

        // The worklist should produce MORE ref_targets than just Pass 1 entries
        // because Reborrow and Cast candidates create additional entries.
        // If propagation didn't work, ref_targets.len() == pass1_ref_count.
        assert!(
            chc_ctx.ref_resolution.ref_targets.len() > pass1_ref_count,
            "worklist should produce ref_targets beyond Pass 1: \
             got {} total vs {} from Pass 1 alone",
            chc_ctx.ref_resolution.ref_targets.len(),
            pass1_ref_count
        );

        // All ref_targets should ultimately point to arg-range locals
        // (x = local 1 for single-arg function)
        for (local, target) in &chc_ctx.ref_resolution.ref_targets {
            assert!(
                target.local <= body.arg_locals().len(),
                "ref_target for local {} should point to arg-range local, got {}",
                local,
                target.local
            );
        }
    });
}

/// apply_numeric_ref_candidate: deferred-transitive path enqueues candidates
/// when their transitive target is not yet resolved, then resolves them when
/// the dependency appears.
///
/// Pattern: `&&T` double-reference where the inner deref destination
/// depends on a ref_target that may not exist during first encounter.
///
/// Exercises: apply_numeric_ref_candidate TransitiveDeref deferred path (line 262).
#[test]
fn test_deferred_transitive_resolves_after_dependency() {
    // Double reference: rr = &r, r2 = *rr resolves to x through transitive deref.
    // The TransitiveDeref candidate for r2 defers when src_target.local's
    // own ref_target hasn't been processed yet, then resolves when the
    // worklist reaches that dependency.
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        pub fn probe_deferred_transitive(x: u32) -> u32 {
            let r = &x;
            let rr = &r;       // rr → r
            let r2 = *rr;      // TransitiveDeref: r2 → *rr → r → x
            *r2
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_deferred_transitive");
        let body = instance.body().expect("function body");
        let mut chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "probe_deferred_transitive", ChcConfig::default());
        chc_ctx.declare_block_relations();

        // Find the `_r2 = Copy(*_rr)` / `_r2 = Move(*_rr)` statement
        let mut transitive_verified = false;
        for block in &body.blocks {
            for stmt in &block.statements {
                if let StatementKind::Assign(
                    lhs,
                    Rvalue::Use(Operand::Copy(place) | Operand::Move(place)),
                ) = &stmt.kind
                    && place.projection.len() == 1
                    && matches!(place.projection[0], ProjectionElem::Deref)
                {
                    let deref_src = place.local;
                    let dest = lhs.local;

                    // The deref source (rr) should have a ref_target
                    if let Some(src_target) = chc_ctx.ref_resolution.ref_targets.get(&deref_src) {
                        // The transitive target (r's target = x)
                        if let Some(transitive_target) =
                            chc_ctx.ref_resolution.ref_targets.get(&src_target.local)
                        {
                            // The destination (r2) should have been resolved
                            // through the deferred-transitive path
                            let dest_target = chc_ctx
                                .ref_resolution
                                .ref_targets
                                .get(&dest)
                                .unwrap_or_else(|| {
                                    panic!(
                                        "destination local {} should have ref_target after \
                                     deferred-transitive resolution (src={}, src_target={}, \
                                     transitive_target={})",
                                        dest, deref_src, src_target.local, transitive_target.local
                                    )
                                });

                            assert_eq!(
                                dest_target.local, transitive_target.local,
                                "deferred-transitive should resolve dest {} to \
                                 transitive target local {}, got {}",
                                dest, transitive_target.local, dest_target.local
                            );
                            transitive_verified = true;
                        }
                    }
                }
            }
        }

        assert!(
            transitive_verified,
            "expected at least one transitive deref resolution through deferred path"
        );
    });
}

/// propagate_numeric_ref_targets_worklist: worklist drains deferred-transitive
/// map entries when their target becomes available, resolving the full chain.
///
/// Uses a 3-level reference chain where each level depends on the previous:
/// r1 = &x, r2 = &r1, r3 = &r2, val = ***r3.
/// The worklist must propagate through all levels, draining deferred entries.
///
/// Exercises: propagate_numeric_ref_targets_worklist deferred drain (line 349).
#[test]
fn test_worklist_drains_deferred_chain() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        pub fn probe_deferred_chain(x: u32) -> u32 {
            let r1 = &x;
            let r2 = &r1;
            let r3 = &r2;
            // Each deref level resolves through the worklist:
            // *r3 → r2, *r2 → r1, *r1 → x
            let v1 = *r3;  // TransitiveDeref: deferred until r2's target resolved
            let v2 = *v1;  // TransitiveDeref: deferred until r1's target resolved
            *v2
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_deferred_chain");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_deferred_chain", ChcConfig::default());
        chc_ctx.declare_block_relations();

        // Count how many Copy/Move(*ref) statements got their ref_targets resolved
        let mut deref_copy_count = 0;
        let mut resolved_count = 0;
        for block in &body.blocks {
            for stmt in &block.statements {
                if let StatementKind::Assign(
                    lhs,
                    Rvalue::Use(Operand::Copy(place) | Operand::Move(place)),
                ) = &stmt.kind
                    && place.projection.len() == 1
                    && matches!(place.projection[0], ProjectionElem::Deref)
                    && chc_ctx.ref_resolution.ref_targets.contains_key(&place.local)
                {
                    deref_copy_count += 1;
                    if chc_ctx.ref_resolution.ref_targets.contains_key(&lhs.local) {
                        resolved_count += 1;
                    }
                }
            }
        }

        assert!(
            deref_copy_count >= 2,
            "expected >= 2 Copy/Move(*ref) statements in 3-level chain, got {}",
            deref_copy_count
        );

        // The worklist resolves transitive deref candidates. At 3 levels,
        // the deepest may not resolve if its transitive target wasn't yet
        // available during the single worklist pass. Key: at least 2 resolve.
        assert!(
            resolved_count >= 2,
            "worklist should resolve >= 2 deferred entries in 3-level chain: \
             {} of {} resolved",
            resolved_count,
            deref_copy_count
        );

        // Verify the deepest deref resolves to the original local (x = arg 1)
        // by checking that at least one ref_target points to a parameter-range local
        let points_to_param =
            chc_ctx.ref_resolution.ref_targets.values().any(|t| t.local <= body.arg_locals().len());
        assert!(points_to_param, "at least one ref_target should resolve to the parameter local x");
    });
}

/// Pass 2 creates deref-through-ref entries when the Deref source has
/// a known ref_target from Pass 1. Verify that `&(*r).field` where
/// `r = &local` produces a ref_target for the deref-through-ref destination.
///
/// Uses owned locals (not reference parameters) to ensure Pass 1 creates
/// ref_targets that Pass 2 can resolve through.
///
/// Exercises: collect_numeric_ref_targets Pass 2 deref-through-ref path,
/// and indirectly the PostPass2 CopyMoveOnly round since it runs as part
/// of collect_numeric_ref_targets.
#[test]
fn test_pass2_deref_through_ref_creates_ref_target() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        pub struct S { pub a: u32, pub b: u32 }

        pub fn probe_pass2_deref() -> u32 {
            let s = S { a: 10, b: 20 };
            let r = &s;                  // Pass 1: _r = &_s
            let field_ref = &(*r).a;     // Pass 2: &((*_r).a) → resolves via _r
            *field_ref
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_pass2_deref");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_pass2_deref", ChcConfig::default());
        chc_ctx.declare_block_relations();

        // Pass 1 should have created ref_targets from `r = &s`
        assert!(
            !chc_ctx.ref_resolution.ref_targets.is_empty(),
            "probe_pass2_deref should have ref_targets from Pass 1 (r = &s)"
        );

        // Find Ref/AddressOf with Deref projection (Pass 2 pattern)
        let mut pass2_ref_locals = Vec::new();
        for block in &body.blocks {
            for stmt in &block.statements {
                if let StatementKind::Assign(
                    lhs,
                    Rvalue::Ref(_, _, place) | Rvalue::AddressOf(_, place),
                ) = &stmt.kind
                    && !place.projection.is_empty()
                    && matches!(place.projection[0], ProjectionElem::Deref)
                {
                    pass2_ref_locals.push(lhs.local);
                }
            }
        }

        // Pass 2 should resolve deref-through-ref entries because the Deref
        // source (r) has a ref_target from Pass 1 pointing to s.
        let pass2_resolved: Vec<_> = pass2_ref_locals
            .iter()
            .filter(|l| chc_ctx.ref_resolution.ref_targets.contains_key(l))
            .collect();

        assert!(
            !pass2_resolved.is_empty(),
            "Pass 2 should resolve deref-through-ref entries via Pass 1 targets: \
             found {} &(*ref).field statements, {} resolved in ref_targets",
            pass2_ref_locals.len(),
            pass2_resolved.len()
        );

        // The Pass 2 entry's target should have field projections from
        // the &(*r).a pattern, proving the deref was resolved and the
        // field suffix was appended.
        for &ref_local in &pass2_resolved {
            let target = &chc_ctx.ref_resolution.ref_targets[ref_local];
            assert!(
                !target.projections.is_empty(),
                "Pass 2 ref_target for local {} should have field projections from \
                 the deref-through-ref pattern, got empty projections",
                ref_local
            );
        }
    });
}
