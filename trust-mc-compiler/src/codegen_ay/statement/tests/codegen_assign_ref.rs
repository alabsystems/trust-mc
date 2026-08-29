// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Dedicated MIR-driven tests for `codegen_assign_ref.rs`.
//!
//! Covers core paths in the extracted ref-assignment tracking module:
//! - happy path: constant reference assignment creates synthetic pointee tracking
//! - no-op/error path: non-reference constants do not create synthetic pointees
//! - propagation path: Copy/Move reference chains preserve pointee mappings
//!
//! Part of #2382 (dedicated coverage for statement/codegen_assign_ref.rs).

use super::*;
use std::sync::Arc;

/// Seed argument locals into SSA environment with symbolic variables.
fn seed_args(codegen: &mut StatementCodegen<'_, '_, '_>, body: &rustc_public::mir::Body) {
    for (idx, local_decl) in body.arg_locals().iter().enumerate() {
        let local_idx = idx + 1;
        let local = Local::from(local_idx);
        let place = Place { local, projection: vec![] };
        let base = codegen.ssa_base_name(&place);
        if let Some(sort) = StatementCodegen::infer_sort_from_ty(local_decl.ty) {
            codegen.env_update(base, Expr::var(format!("arg_{local_idx}"), sort));
        } else {
            codegen.env_update(
                base,
                Expr::var(format!("arg_{local_idx}"), Sort::bitvec(POINTER_WIDTH)),
            );
        }
    }
}

fn walk_all_statements(
    codegen: &mut StatementCodegen<'_, '_, '_>,
    body: &rustc_public::mir::Body,
) -> usize {
    let mut processed = 0;
    for bb in &body.blocks {
        for stmt in &bb.statements {
            codegen.codegen_statement(stmt);
            processed += 1;
        }
    }
    processed
}

const ASSIGN_REF_SOURCE: &str = r#"
pub fn const_ref_probe() -> u32 {
    let r = &42u32;
    *r
}

pub fn scalar_const_only() -> u32 {
    let x = 7u32;
    x
}

pub fn ref_copy_chain(x: &u32) -> u32 {
    let r1 = x;
    let r2 = r1;
    *r2
}
"#;

/// Happy path: `let r = &CONST` should allocate a synthetic const pointee.
#[test]
fn test_codegen_assign_ref_const_reference_creates_synthetic_pointee() {
    with_test_ay_ctx_for_source(ASSIGN_REF_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "const_ref_probe");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);
        seed_args(&mut codegen, &body);

        let counter_before = codegen.synthetic_pointee_counter;
        let processed = walk_all_statements(&mut codegen, &body);
        assert!(processed > 0, "const_ref_probe should process at least one statement");

        assert!(
            codegen.synthetic_pointee_counter > counter_before,
            "const reference should increment synthetic_pointee_counter"
        );
        assert!(
            codegen.ref_pointees.values().any(|v| v.contains("const_pointee_")),
            "const reference should register a const_pointee mapping"
        );
    });
}

/// No-op/error path: non-reference constants should not create synthetic pointees.
#[test]
fn test_codegen_assign_ref_non_reference_constant_does_not_create_synthetic_pointee() {
    with_test_ay_ctx_for_source(ASSIGN_REF_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "scalar_const_only");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);
        seed_args(&mut codegen, &body);

        let has_non_ref_constant_assign =
            body.blocks.iter().flat_map(|bb| bb.statements.iter()).any(|stmt| {
                matches!(
                    &stmt.kind,
                    StatementKind::Assign(_, Rvalue::Use(Operand::Constant(c)))
                        if !matches!(c.const_.ty().kind(), TyKind::RigidTy(RigidTy::Ref(..)))
                )
            });
        assert!(
            has_non_ref_constant_assign,
            "scalar_const_only should contain at least one non-reference constant assignment"
        );

        let counter_before = codegen.synthetic_pointee_counter;
        let processed = walk_all_statements(&mut codegen, &body);
        assert!(processed > 0, "scalar_const_only should process at least one statement");

        assert_eq!(
            codegen.synthetic_pointee_counter, counter_before,
            "non-reference constants must not increment synthetic_pointee_counter"
        );
        assert!(
            !codegen.ref_pointees.values().any(|v| v.contains("const_pointee_")),
            "non-reference constants must not register const_pointee mappings"
        );
    });
}

/// Copy/Move propagation path: `r2 = r1` should preserve pointee mapping.
#[test]
fn test_codegen_assign_ref_copy_move_propagates_pointee_mapping() {
    with_test_ay_ctx_for_source(ASSIGN_REF_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "ref_copy_chain");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);
        seed_args(&mut codegen, &body);

        let src_place = Place { local: Local::from(1usize), projection: vec![] };
        let dst_place = Place { local: Local::from(999usize), projection: vec![] };

        let src_base = codegen.ssa_base_name(&src_place);
        let dst_base = codegen.ssa_base_name(&dst_place);
        let expected_pointee: Arc<str> = Arc::from("manual_ref_target");
        codegen.ref_pointees.insert(Arc::from(src_base), Arc::clone(&expected_pointee));

        let rhs = Rvalue::Use(Operand::Copy(src_place));
        codegen.track_copy_move_ref_pointees(&dst_place, &rhs);

        assert_eq!(
            codegen.ref_pointees.get(dst_base.as_str()),
            Some(&expected_pointee),
            "copy/move propagation should copy ref_pointees mapping to destination"
        );
    });
}

/// CopyForDeref propagation path: rustc uses `CopyForDeref(_ref)` for wrapper
/// peeling before deref, and the temporary must preserve the pointee mapping.
#[test]
fn test_codegen_assign_ref_copy_for_deref_propagates_pointee_mapping() {
    with_test_ay_ctx_for_source(ASSIGN_REF_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "ref_copy_chain");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);
        seed_args(&mut codegen, &body);

        let src_place = Place { local: Local::from(1usize), projection: vec![] };
        let dst_place = Place { local: Local::from(999usize), projection: vec![] };

        let src_base = codegen.ssa_base_name(&src_place);
        let dst_base = codegen.ssa_base_name(&dst_place);
        let expected_pointee: Arc<str> = Arc::from("manual_copy_for_deref_target");
        codegen.ref_pointees.insert(Arc::from(src_base), Arc::clone(&expected_pointee));

        let rhs = Rvalue::CopyForDeref(src_place);
        codegen.track_copy_move_ref_pointees(&dst_place, &rhs);

        assert_eq!(
            codegen.ref_pointees.get(dst_base.as_str()),
            Some(&expected_pointee),
            "CopyForDeref propagation should copy ref_pointees mapping to destination"
        );
    });
}

/// Copy/Move of a composite wrapper should preserve nested ref field metadata.
#[test]
fn test_codegen_assign_ref_copy_move_propagates_nested_pointee_mapping() {
    with_test_ay_ctx_for_source(ASSIGN_REF_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "ref_copy_chain");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);
        seed_args(&mut codegen, &body);

        let src_place = Place { local: Local::from(1usize), projection: vec![] };
        let dst_place = Place { local: Local::from(999usize), projection: vec![] };

        let src_base = codegen.ssa_base_name(&src_place);
        let dst_base = codegen.ssa_base_name(&dst_place);
        let expected_pointee: Arc<str> = Arc::from("manual_nested_ref_target");
        codegen
            .ref_pointees
            .insert(Arc::from(format!("{src_base}_field_0")), Arc::clone(&expected_pointee));

        let rhs = Rvalue::Use(Operand::Copy(src_place));
        codegen.track_copy_move_ref_pointees(&dst_place, &rhs);

        assert_eq!(
            codegen.ref_pointees.get(format!("{dst_base}_field_0").as_str()),
            Some(&expected_pointee),
            "copy/move propagation should copy nested ref_pointees metadata to the destination"
        );
    });
}

// -----------------------------------------------------------------------------
// track_ref_pointees — Ref/AddressOf rvalue tracking
// Acceptance criteria: #2411 codegen_assign_ref.rs coverage
// -----------------------------------------------------------------------------

const REF_TRACKING_SOURCE: &str = r#"
pub fn ref_pointee_probe(x: u32) -> u32 {
    let r = &x;
    *r
}

pub fn mut_ref_deref_probe(r: &mut u32) {
    *r = 42;
}
"#;

/// Test that `track_ref_pointees` inserts a ref_pointees mapping for `Rvalue::Ref`.
///
/// Exercises the production function `track_ref_pointees` from codegen_assign_ref.rs.
#[test]
fn test_track_ref_pointees_creates_mapping_for_ref_rvalue() {
    with_test_ay_ctx_for_source(REF_TRACKING_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "ref_pointee_probe");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);
        seed_args(&mut codegen, &body);

        // Find the Ref rvalue statement in MIR: `_ref = &_x`
        let mut found_ref = false;
        for bb in &body.blocks {
            for stmt in &bb.statements {
                let StatementKind::Assign(lhs, rvalue) = &stmt.kind else {
                    continue;
                };
                if !matches!(rvalue, Rvalue::Ref(..)) {
                    continue;
                }
                let ref_base = codegen.ssa_base_name(lhs);
                assert!(
                    !codegen.ref_pointees.contains_key(ref_base.as_str()),
                    "ref_pointees should be empty before track_ref_pointees call"
                );
                codegen.track_ref_pointees(lhs, rvalue);
                assert!(
                    codegen.ref_pointees.contains_key(ref_base.as_str()),
                    "track_ref_pointees must insert a mapping for Ref rvalue"
                );
                found_ref = true;
                break;
            }
            if found_ref {
                break;
            }
        }
        assert!(found_ref, "MIR for ref_pointee_probe should contain a Rvalue::Ref");
    });
}

/// Test that `try_codegen_assign_ref_deref` handles `*r = value` for mutable references.
///
/// Directly calls `try_codegen_assign_ref_deref` from codegen_assign_ref.rs on the
/// deref-assignment statement in `mut_ref_deref_probe`. Verifies the function returns
/// true (handled) and updates the pointee in the environment.
#[test]
fn test_try_codegen_assign_ref_deref_handles_mutable_ref() {
    with_test_ay_ctx_for_source(REF_TRACKING_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "mut_ref_deref_probe");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);
        seed_args(&mut codegen, &body);

        // First pass: walk all statements to populate environment and ref_pointees
        walk_all_statements(&mut codegen, &body);

        // Find the Deref assignment statement: `*_ref = value`
        let mut found_and_handled = false;
        for bb in &body.blocks {
            for stmt in &bb.statements {
                let StatementKind::Assign(lhs, rvalue) = &stmt.kind else {
                    continue;
                };
                if !matches!(lhs.projection.first(), Some(ProjectionElem::Deref)) {
                    continue;
                }
                // This LHS is `*_something` — directly call try_codegen_assign_ref_deref
                let handled = codegen.try_codegen_assign_ref_deref(lhs, rvalue);
                if handled {
                    found_and_handled = true;
                    break;
                }
            }
            if found_and_handled {
                break;
            }
        }

        // Assert the deref assignment was found AND handled by the production function.
        // MIR for `*r = 42` must contain a Deref projection on the LHS.
        assert!(
            found_and_handled,
            "try_codegen_assign_ref_deref must find and handle the `*r = 42` deref assignment"
        );
    });
}

/// Test that `track_ref_pointees` is a no-op for non-Ref/non-AddressOf rvalues.
#[test]
fn test_track_ref_pointees_ignores_non_ref_rvalues() {
    with_test_ay_ctx_for_source(ASSIGN_REF_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "scalar_const_only");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);
        seed_args(&mut codegen, &body);

        let before = codegen.ref_pointees.len();

        // Walk all assignments and call track_ref_pointees on non-Ref rvalues
        for bb in &body.blocks {
            for stmt in &bb.statements {
                let StatementKind::Assign(lhs, rvalue) = &stmt.kind else {
                    continue;
                };
                if matches!(rvalue, Rvalue::Ref(..) | Rvalue::AddressOf(..)) {
                    continue;
                }
                codegen.track_ref_pointees(lhs, rvalue);
            }
        }

        assert_eq!(
            codegen.ref_pointees.len(),
            before,
            "track_ref_pointees must be a no-op for non-Ref/non-AddressOf rvalues"
        );
    });
}

// =============================================================================
// deref_pointee_alias — canonical referent naming for `&(*r).field`
// =============================================================================

const DEREF_BORROW_SOURCE: &str = r#"
pub struct Pair { pub a: u32, pub b: u32 }

pub fn borrow_first(p: &mut Pair) -> &mut u32 {
    &mut p.a
}
"#;

/// `&mut (*_r).0` must name the referent after the STORAGE the deref ladder
/// resolves (`ref_pointees[_r]` + `_field_0`), not after the reference local it
/// was reached through (`local_{r}_deref_field_0`).
///
/// Two reference locals that alias the same place otherwise get two unrelated
/// env slots, so a store through one is invisible to a load through the other
/// (`history/clone_pass`: the ensures read `ptr.0` from one slot while `ptr.0 +=
/// 1` had written another, and a TRUE contract was reported FAILED).
#[test]
fn test_track_ref_pointees_canonicalizes_deref_field_borrow() {
    with_test_ay_ctx_for_source(DEREF_BORROW_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "borrow_first");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);
        seed_args(&mut codegen, &body);

        // The deref ladder resolves `_1` to a canonical storage base.
        let arg = Place { local: Local::from(1usize), projection: vec![] };
        let arg_base = codegen.ssa_base_name(&arg);
        codegen.ref_pointees.insert(Arc::from(arg_base.as_str()), Arc::from("canon::local_2"));

        let mut found = false;
        for bb in &body.blocks {
            for stmt in &bb.statements {
                let StatementKind::Assign(lhs, rvalue) = &stmt.kind else {
                    continue;
                };
                let (Rvalue::Ref(_, _, pointee) | Rvalue::AddressOf(_, pointee)) = rvalue else {
                    continue;
                };
                if !matches!(pointee.projection.first(), Some(ProjectionElem::Deref)) {
                    continue;
                }
                let ref_base = codegen.ssa_base_name(lhs);
                codegen.track_ref_pointees(lhs, rvalue);
                let mapped = codegen
                    .ref_pointees
                    .get(ref_base.as_str())
                    .expect("borrow must record a pointee")
                    .to_string();
                assert_eq!(
                    mapped, "canon::local_2_field_0",
                    "`&mut (*_1).0` must resolve to the canonical storage name"
                );
                found = true;
                break;
            }
            if found {
                break;
            }
        }
        assert!(found, "borrow_first MIR should contain `&mut (*_1).0`");
    });
}

/// Control (opposite direction): with NO `ref_pointees` entry for the reference
/// local there is nothing to canonicalize against, so the borrow keeps the old
/// syntactic name. The alias is derived, never invented.
#[test]
fn test_track_ref_pointees_keeps_syntactic_name_without_resolution() {
    with_test_ay_ctx_for_source(DEREF_BORROW_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "borrow_first");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);
        seed_args(&mut codegen, &body);
        // Drop every resolution, INCLUDING the `arg_pointee_*` seeds
        // `StatementCodegen::new` installs for reference arguments, so the
        // canonicalization has nothing to derive from.
        codegen.ref_pointees.clear();

        let mut found = false;
        for bb in &body.blocks {
            for stmt in &bb.statements {
                let StatementKind::Assign(lhs, rvalue) = &stmt.kind else {
                    continue;
                };
                let (Rvalue::Ref(_, _, pointee) | Rvalue::AddressOf(_, pointee)) = rvalue else {
                    continue;
                };
                if !matches!(pointee.projection.first(), Some(ProjectionElem::Deref)) {
                    continue;
                }
                let ref_base = codegen.ssa_base_name(lhs);
                let syntactic = codegen.ssa_base_name(pointee);
                codegen.track_ref_pointees(lhs, rvalue);
                let mapped = codegen
                    .ref_pointees
                    .get(ref_base.as_str())
                    .expect("borrow must record a pointee")
                    .to_string();
                assert_eq!(
                    mapped, syntactic,
                    "with no resolution available the syntactic name must stand"
                );
                found = true;
                break;
            }
            if found {
                break;
            }
        }
        assert!(found, "borrow_first MIR should contain `&mut (*_1).0`");
    });
}
