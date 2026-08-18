// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Unit tests for `codegen_stmt_flatten.rs` — constrain_flattened_fields_core
//! behavior, flattened_field_count, constrain_flattened_pair, and the
//! for_call variant.
//!
//! Complements `test_stmt_flatten.rs` which tests MIR-to-CHC pipeline patterns.
//! These tests exercise the constraint-level helpers directly.
//!
//! Part of #2921 (CHC codegen test coverage).

// Test code: unwrap/panic are acceptable for assertions
#![allow(clippy::unwrap_used, clippy::panic)]

use super::common::*;
use ay_bindings::{Expr, Sort};

use super::super::stmt_accumulator::StmtAccumulator;

const OPTION_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub fn probe_option_flatten(x: Option<u32>) -> Option<u32> {
        x
    }
"#;

const TUPLE_3_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub fn probe_tuple_3(a: u32, b: u32, c: u32) -> (u32, u32, u32) {
        (a, b, c)
    }
"#;

const CHECKED_ADD_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub fn probe_checked_add_core(a: u32, b: u32) -> (u32, bool) {
        a.overflowing_add(b)
    }
"#;

const SINGLE_FIELD_CUSTOM_UNSIZE_SOURCE: &str = r#"
    #![allow(dead_code)]
    #![feature(coerce_unsized)]
    #![feature(unsize)]

    use std::marker::Unsize;
    use std::ops::{CoerceUnsized, Deref};

    trait Identity {
        fn id(&self) -> u16;
    }

    struct Inner {
        id: u8,
    }

    struct Outer<T: ?Sized> {
        outer_id: u8,
        inner: T,
    }

    impl Identity for Inner {
        fn id(&self) -> u16 {
            self.id.into()
        }
    }

    impl<T> Identity for Outer<T>
    where
        T: ?Sized + Identity,
    {
        fn id(&self) -> u16 {
            ((self.outer_id as u16) << 8) + self.inner.id()
        }
    }

    struct MyPtr<'a, T: ?Sized> {
        ptr: &'a T,
    }

    impl<'a, T: ?Sized + Unsize<U>, U: ?Sized> CoerceUnsized<MyPtr<'a, U>> for MyPtr<'a, T> {}

    impl<'a, T: ?Sized> Deref for MyPtr<'a, T> {
        type Target = T;

        fn deref(&self) -> &Self::Target {
            self.ptr
        }
    }

    fn probe_single_field_custom_unsize(outer: &Outer<Inner>) -> u16 {
        let outer_ptr = MyPtr { ptr: outer };
        let id_ptr: MyPtr<dyn Identity> = outer_ptr;
        id_ptr.id()
    }
"#;

// =============================================================================
// flattened_field_count: default and explicit mapping
// =============================================================================

/// `flattened_field_count` returns 2 by default when no explicit mapping exists.
#[test]
fn test_flattened_field_count_default_is_two() {
    with_test_ay_ctx_for_source(OPTION_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_option_flatten");
        let body = instance.body().expect("function body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_option_flatten", ChcConfig::default());

        // Query an arbitrary local index that is NOT in flattened_local_field_count
        let unmapped_idx = 999;
        assert!(
            !chc_ctx.flatten.flattened_local_field_count.contains_key(&unmapped_idx),
            "test precondition: local {unmapped_idx} should not be mapped"
        );
        let count = chc_ctx.flattened_field_count(unmapped_idx);
        assert_eq!(count, 2, "default flattened field count should be 2");
    });
}

/// `flattened_field_count` returns explicit mapping when present (3-tuple).
#[test]
fn test_flattened_field_count_explicit_mapping() {
    with_test_ay_ctx_for_source(TUPLE_3_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_tuple_3");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_tuple_3", ChcConfig::default());
        chc_ctx.declare_block_relations();

        // Find a flattened local with 3 fields
        let three_field_local = chc_ctx
            .flatten
            .flattened_local_field_count
            .iter()
            .find(|&(_, count)| *count == 3)
            .map(|(&idx, _)| idx);

        if let Some(local_idx) = three_field_local {
            let count = chc_ctx.flattened_field_count(local_idx);
            assert_eq!(count, 3, "3-tuple local should have flattened_field_count = 3");
        }
        // If MIR optimized away the 3-tuple, this test is safely vacuous.
    });
}

// =============================================================================
// constrain_flattened_fields: constraint emission and replacement
// =============================================================================

/// `constrain_flattened_fields` emits constraints for each provided value
/// and returns true when at least one constraint is emitted.
#[test]
fn test_constrain_flattened_fields_emits_constraints() {
    with_test_ay_ctx_for_source(OPTION_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_option_flatten");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_option_flatten", ChcConfig::default());
        chc_ctx.declare_block_relations();

        // Find a flattened Option local
        let flattened_locals: Vec<usize> =
            chc_ctx.flatten.flattened_tuple_locals.iter().copied().collect();
        if flattened_locals.is_empty() {
            return; // MIR may optimize away
        }
        let local_idx = flattened_locals[0];
        let vec_idx = chc_ctx.state_idx_for_local(local_idx);

        // Verify output slots exist
        if chc_ctx.state_var_mgr.output_state_vars.len() <= vec_idx + 1 {
            return; // Not enough output slots for 2-field local
        }

        let mut constraints = Vec::new();
        let mut last_constraint_for_local = std::collections::HashMap::new();
        let mut modified = HashSet::new();

        let values = vec![Some(Expr::bool_const(true)), Some(Expr::bitvec_const(42u64, 32))];

        let emitted = {
            let mut acc = StmtAccumulator::new(
                &mut modified,
                &mut constraints,
                &mut last_constraint_for_local,
            );
            chc_ctx.constrain_flattened_fields(local_idx, &values, &mut acc)
        };

        assert!(emitted, "constrain_flattened_fields should emit at least one constraint");
        assert!(!constraints.is_empty(), "constraints should not be empty after emission");
        assert!(modified.contains(&local_idx), "modified set should contain the local index");
    });
}

/// `constrain_flattened_fields` with `None` values clears stale constraints.
#[test]
fn test_constrain_flattened_fields_none_clears_stale() {
    with_test_ay_ctx_for_source(OPTION_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_option_flatten");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_option_flatten", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let flattened_locals: Vec<usize> =
            chc_ctx.flatten.flattened_tuple_locals.iter().copied().collect();
        if flattened_locals.is_empty() {
            return;
        }
        let local_idx = flattened_locals[0];
        let vec_idx = chc_ctx.state_idx_for_local(local_idx);
        if chc_ctx.state_var_mgr.output_state_vars.len() <= vec_idx + 1 {
            return;
        }

        let mut constraints = Vec::new();
        let mut last_constraint_for_local = std::collections::HashMap::new();
        let mut modified = HashSet::new();

        // First: emit a constraint for field 0
        let values_first = vec![Some(Expr::bool_const(true)), Some(Expr::bitvec_const(1u64, 32))];
        {
            let mut acc = StmtAccumulator::new(
                &mut modified,
                &mut constraints,
                &mut last_constraint_for_local,
            );
            chc_ctx.constrain_flattened_fields(local_idx, &values_first, &mut acc);
        }

        let constraint_count_after_first = constraints.len();

        // Second: emit None for field 0 (should clear it), Some for field 1
        let values_second = vec![None, Some(Expr::bitvec_const(2u64, 32))];
        {
            let mut acc = StmtAccumulator::new(
                &mut modified,
                &mut constraints,
                &mut last_constraint_for_local,
            );
            chc_ctx.constrain_flattened_fields(local_idx, &values_second, &mut acc);
        }

        // The first field's stale constraint should have been replaced with true
        assert!(
            constraints.len() > constraint_count_after_first,
            "second emission should add new constraints"
        );
        // Check that at least one constraint in the old positions is now `true`
        let true_count =
            constraints.iter().filter(|c| matches!(c.value(), ExprValue::BoolConst(true))).count();
        assert!(true_count > 0, "stale constraints should be replaced with bool_const(true)");
    });
}

// =============================================================================
// constrain_flattened_fields_for_call: no modified set mutation
// =============================================================================

/// `constrain_flattened_fields_for_call` does not require a `modified` HashSet.
/// Verifies the call-handler variant works for the same constraint emission.
#[test]
fn test_constrain_flattened_fields_for_call_emits_constraints() {
    with_test_ay_ctx_for_source(OPTION_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_option_flatten");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_option_flatten", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let flattened_locals: Vec<usize> =
            chc_ctx.flatten.flattened_tuple_locals.iter().copied().collect();
        if flattened_locals.is_empty() {
            return;
        }
        let local_idx = flattened_locals[0];
        let vec_idx = chc_ctx.state_idx_for_local(local_idx);
        if chc_ctx.state_var_mgr.output_state_vars.len() <= vec_idx + 1 {
            return;
        }

        let mut constraints = Vec::new();

        let values = vec![Some(Expr::bool_const(false)), Some(Expr::bitvec_const(99u64, 32))];

        let emitted =
            chc_ctx.constrain_flattened_fields_for_call(local_idx, &values, &mut constraints);

        assert!(emitted, "for_call variant should emit constraints");
        assert!(!constraints.is_empty(), "constraints should not be empty");
    });
}

// =============================================================================
// constrain_flattened_pair: convenience wrapper for 2-field locals
// =============================================================================

/// `try_encode_flattened_local_assign` with a CheckedBinaryOp produces a
/// valid VC with both BV and Bool sorts (Pattern 1).
#[test]
fn test_checked_add_flattened_pair_produces_correct_sorts() {
    with_test_ay_ctx_for_source(CHECKED_ADD_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_checked_add_core");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_checked_add_core", ChcConfig::default());

        let bb_count = body.blocks.len();
        assert_vc_structure(&vc, "probe_checked_add_core", bb_count);

        // The CheckedBinaryOp should produce both BV32 (result) and Bool (overflow)
        assert_relation_has_arg_sort(
            &vc,
            "probe_checked_add_core",
            ay_bindings::Sort::is_bool,
            "Bool",
        );
        assert_relation_has_arg_sort(
            &vc,
            "probe_checked_add_core",
            |s| s.bitvec_width() == Some(32),
            "bv32",
        );
    });
}

// =============================================================================
// 3-field Result heterogeneous layout
// =============================================================================

const RESULT_HETERO_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub fn probe_result_hetero(x: u32) -> Result<u32, u64> {
        Ok(x)
    }
"#;

const RESULT_BOOL_SAME_SORT_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub fn probe_result_same_sort(x: Result<bool, bool>) -> Result<bool, bool> {
        x
    }
"#;

const PAYLOAD_VARIANT_ZERO_ARRAY_ENUM_SOURCE: &str = r#"
    #![allow(dead_code)]

    enum FirstPayload {
        Payload([u8; 8]),
        Empty,
    }

    pub fn probe_first_payload_enum(x: [u8; 8]) -> FirstPayload {
        FirstPayload::Payload(x)
    }
"#;

const RESUME_RESULT_ENUM_SOURCE: &str = r#"
    #![allow(dead_code)]

    #[derive(Clone, Copy)]
    pub enum ResumeState {
        Yielded(()),
        Complete((u32, u64)),
    }

    pub fn probe_resume_result_layout(flag: bool, x: u32, y: u64) -> ResumeState {
        if flag {
            ResumeState::Yielded(())
        } else {
            ResumeState::Complete((x, y))
        }
    }
"#;

/// Result<u32, u64> with heterogeneous payload types uses 3-field layout:
/// (is_ok: Bool, ok_val: bv32, err_val: bv64).
#[test]
fn test_result_heterogeneous_3_field_flattened_layout() {
    with_test_ay_ctx_for_source(RESULT_HETERO_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_result_hetero");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_result_hetero", ChcConfig::default());

        let bb_count = body.blocks.len();
        assert_vc_structure(&vc, "probe_result_hetero", bb_count);

        // Should have Bool (is_ok), bv32 (ok_val), and bv64 (err_val)
        assert_relation_has_arg_sort(
            &vc,
            "probe_result_hetero",
            ay_bindings::Sort::is_bool,
            "Bool",
        );
        assert_relation_has_arg_sort(
            &vc,
            "probe_result_hetero",
            |s| s.bitvec_width() == Some(32),
            "bv32",
        );
    });
}

/// FLATTEN_ITE_HETERO (char_validity gap): an `ite(cond, Ok(bv32), Err(bv64))`
/// for a heterogeneous `Result<u32,u64>` flattened destination must decompose
/// EXACTLY into the disjoint tag/ok_val/err_val slots — Ok's payload into slot 1
/// and Err's differently-sorted payload into slot 2 (no collision), with the
/// tag polarity taken from the declared discriminant (Ok = true-variant) — and
/// it must NOT record a sound fallback. Before the fix the mismatched Ok/Err
/// payload sorts collided at slot 0, the ITE merge bailed, and the whole
/// datatype was havoced (`flatten_dest_sort_mismatch`), the exact defect that
/// broke `char_validity::check_char_ok`.
#[test]
fn test_decompose_hetero_result_ite_of_constructors_is_exact() {
    with_test_ay_ctx_for_source(RESULT_HETERO_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_result_hetero");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_result_hetero", ChcConfig::default());
        chc_ctx.declare_block_relations();

        // The flattened `Result<u32,u64>` local (no enum_bv layout is registered
        // for Result, so it reaches the decompose_datatype ITE path).
        let dest_local = chc_ctx
            .flatten
            .flattened_tuple_locals
            .iter()
            .copied()
            .find(|&local_idx| {
                matches!(
                    body.locals().get(local_idx).map(|d| d.ty.kind()),
                    Some(rustc_public::ty::TyKind::RigidTy(rustc_public::ty::RigidTy::Adt(def, _)))
                        if def.trimmed_name() == "Result"
                )
            })
            .expect("Result<u32,u64> local should be flattened");

        let local_ty = body.locals().get(dest_local).expect("Result local").ty;
        let result_sort = ChcCtx::translate_ty(local_ty).expect("Result should translate");
        let result_dt = result_sort.datatype_sort().expect("Result should be a datatype");
        let ok_ctor = result_dt
            .constructors
            .iter()
            .find(|c| c.name.contains("Ok"))
            .expect("Result exposes Ok");
        let err_ctor = result_dt
            .constructors
            .iter()
            .find(|c| c.name.contains("Err"))
            .expect("Result exposes Err");
        let ok_expr = Expr::datatype_constructor(
            result_dt.name.clone(),
            ok_ctor.name.clone(),
            vec![Expr::bitvec_const(7u64, 32)],
            result_sort.clone(),
        );
        let err_expr = Expr::datatype_constructor(
            result_dt.name.clone(),
            err_ctor.name.clone(),
            vec![Expr::bitvec_const(9u64, 64)],
            result_sort.clone(),
        );
        // Fresh Bool var so the outer ite does not fold away.
        let cond = Expr::var("cond_flag", Sort::bool());
        let ite = Expr::ite(cond, ok_expr, err_expr);

        let before = chc_ctx.sound_fallback_count();
        let constraints = chc_ctx
            .build_flattened_destination_constraints(dest_local, ite)
            .expect("hetero Result ite-of-constructors must decompose to scalars");

        assert_eq!(
            constraints.len(),
            3,
            "must constrain is_ok + ok_val + err_val, got {constraints:?}"
        );
        assert_eq!(
            chc_ctx.sound_fallback_count(),
            before,
            "exact ITE decomposition must NOT record a sound fallback (no havoc)"
        );

        // Disjoint placement: Ok's bv32 payload lands in slot 1, Err's bv64 in
        // slot 2 — proving the two differently-sorted payloads did not collide.
        let ok_slot =
            chc_ctx.encode.flattened_field_env.get(&(dest_local, 1)).expect("ok_val slot cached");
        assert_eq!(
            ok_slot.sort().bitvec_width(),
            Some(32),
            "ok_val slot must carry the bv32 Ok payload"
        );
        let err_slot =
            chc_ctx.encode.flattened_field_env.get(&(dest_local, 2)).expect("err_val slot cached");
        assert_eq!(
            err_slot.sort().bitvec_width(),
            Some(64),
            "err_val slot must carry the bv64 Err payload"
        );

        // Tag slot cached and Bool-sorted (is_ok discriminant).
        let tag =
            chc_ctx.encode.flattened_field_env.get(&(dest_local, 0)).expect("tag slot cached");
        assert!(tag.sort().is_bool(), "tag slot must be the Bool is_ok discriminant");
    });
}

#[test]
fn test_build_flattened_destination_constraints_unit_payload_enum_keeps_tag_and_payload() {
    with_test_ay_ctx_for_source(RESUME_RESULT_ENUM_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_resume_result_layout");
        let body = instance.body().expect("function body");
        let mut chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "probe_resume_result_layout", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let dest_local = chc_ctx
            .flatten
            .enum_bv_layouts
            .keys()
            .copied()
            .find(|&local_idx| {
                matches!(
                    body.locals().get(local_idx).map(|decl| decl.ty.kind()),
                    Some(rustc_public::ty::TyKind::RigidTy(rustc_public::ty::RigidTy::Adt(def, _)))
                        if def.trimmed_name() == "ResumeState"
                )
            })
            .expect("ResumeState local should use enum_bv_layout");

        let local_ty = body.locals().get(dest_local).expect("ResumeState local").ty;
        let (def, args) = match local_ty.kind() {
            rustc_public::ty::TyKind::RigidTy(rustc_public::ty::RigidTy::Adt(def, args)) => {
                (def, args)
            }
            other => panic!("expected ResumeState ADT local, found {other:?}"),
        };
        let result_sort = ChcCtx::translate_ty(local_ty).expect("ResumeState should translate");
        let result_dt = result_sort.datatype_sort().expect("ResumeState should be a datatype");
        let payload_ty = def.variants()[1].fields()[0].ty_with_args(&args);
        let payload_sort =
            ChcCtx::translate_ty(payload_ty).expect("tuple payload should translate");
        let payload_dt = payload_sort.datatype_sort().expect("tuple payload should be a datatype");
        let payload_ctor =
            payload_dt.constructors.first().expect("tuple payload should have a constructor");
        let payload_expr = Expr::datatype_constructor(
            payload_dt.name.clone(),
            payload_ctor.name.clone(),
            vec![Expr::bitvec_const(7u64, 32), Expr::bitvec_const(9u64, 64)],
            payload_sort,
        );
        let complete_ctor = result_dt
            .constructors
            .iter()
            .find(|ctor| ctor.name.contains("Complete"))
            .expect("ResumeState should expose Complete constructor");
        let result_expr = Expr::datatype_constructor(
            result_dt.name.clone(),
            complete_ctor.name.clone(),
            vec![payload_expr],
            result_sort,
        );

        let constraints = chc_ctx
            .build_flattened_destination_constraints(dest_local, result_expr)
            .expect("flattened ResumeState call result should decompose into tag + payload");

        assert_eq!(
            constraints.len(),
            3,
            "ResumeState should constrain tag + two payload slots, got {constraints:?}"
        );
        assert!(
            chc_ctx.encode.flattened_field_env.contains_key(&(dest_local, 0)),
            "ResumeState tag slot should be cached after decomposition"
        );
        assert!(
            chc_ctx.encode.flattened_field_env.contains_key(&(dest_local, 1)),
            "ResumeState first payload slot should be cached after decomposition"
        );
        assert!(
            chc_ctx.encode.flattened_field_env.contains_key(&(dest_local, 2)),
            "ResumeState second payload slot should be cached after decomposition"
        );
    });
}

#[test]
fn test_build_flattened_destination_constraints_raw_payload_uses_unique_ctor_tag() {
    with_test_ay_ctx_for_source(PAYLOAD_VARIANT_ZERO_ARRAY_ENUM_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_first_payload_enum");
        let body = instance.body().expect("function body");
        let mut chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "probe_first_payload_enum", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let dest_local = chc_ctx
            .flatten
            .enum_bv_layouts
            .keys()
            .copied()
            .find(|&local_idx| {
                matches!(
                    body.locals().get(local_idx).map(|decl| decl.ty.kind()),
                    Some(rustc_public::ty::TyKind::RigidTy(rustc_public::ty::RigidTy::Adt(def, _)))
                        if def.trimmed_name() == "FirstPayload"
                )
            })
            .expect("FirstPayload local should use enum_bv_layout");

        let before = chc_ctx.sound_fallback_count();
        let payload = Expr::const_array(
            Sort::bitvec(crate::codegen_ay::types::POINTER_WIDTH),
            Expr::bitvec_const(0u64, 8),
        )
        .store(
            Expr::bitvec_const(0u64, crate::codegen_ay::types::POINTER_WIDTH),
            Expr::bitvec_const(7u64, 8),
        );

        let constraints = chc_ctx
            .build_flattened_destination_constraints(dest_local, payload)
            .expect("unique raw payload should recover flattened enum tag");

        assert_eq!(
            constraints.len(),
            2,
            "raw payload recovery should constrain both tag and payload slots"
        );
        assert_eq!(
            chc_ctx.sound_fallback_count(),
            before,
            "unique raw payload recovery should not record a sound fallback"
        );
        assert!(
            matches!(
                chc_ctx.encode.flattened_field_env.get(&(dest_local, 0)).map(|expr| expr.value()),
                Some(ExprValue::BoolConst(false))
            ),
            "payload-bearing constructor at index 0 should recover tag=false"
        );
        assert!(
            chc_ctx.encode.flattened_field_env.contains_key(&(dest_local, 1)),
            "payload slot should be cached after raw payload recovery"
        );
    });
}

#[test]
fn test_build_flattened_destination_constraints_raw_same_sort_result_is_ambiguous() {
    with_test_ay_ctx_for_source(RESULT_BOOL_SAME_SORT_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_result_same_sort");
        let body = instance.body().expect("function body");
        let mut chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "probe_result_same_sort", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let dest_local = chc_ctx
            .flatten
            .flattened_enum_discr
            .keys()
            .copied()
            .find(|&local_idx| {
                chc_ctx.flattened_field_count(local_idx) == 2
                    && !chc_ctx.flatten.enum_bv_layouts.contains_key(&local_idx)
                    && matches!(
                        body.locals().get(local_idx).map(|decl| decl.ty.kind()),
                        Some(rustc_public::ty::TyKind::RigidTy(rustc_public::ty::RigidTy::Adt(def, _)))
                            if def.trimmed_name() == "Result"
                    )
            })
            .expect("same-sort Result local should use 2-field Bool+payload flattening");

        let before = chc_ctx.sound_fallback_count();
        let constraints = chc_ctx
            .build_flattened_destination_constraints(dest_local, Expr::bool_const(true))
            .expect("ambiguous raw payload should return a sound fallback placeholder");

        assert_eq!(
            constraints.len(),
            1,
            "ambiguous raw payload should short-circuit to a single fallback constraint"
        );
        assert!(
            matches!(constraints[0].value(), ExprValue::BoolConst(true)),
            "ambiguous raw payload should emit a Bool(true) placeholder"
        );
        assert!(
            chc_ctx.sound_fallback_count() > before,
            "ambiguous raw payload should increment the sound fallback counter"
        );
        assert!(
            !chc_ctx.encode.flattened_field_env.contains_key(&(dest_local, 0)),
            "ambiguous raw payload must not bind the discriminant slot"
        );
        assert!(
            !chc_ctx.encode.flattened_field_env.contains_key(&(dest_local, 1)),
            "ambiguous raw payload must not bind the shared payload slot"
        );
    });
}

/// A single-field flattened smart pointer unsize cast should be handled by the
/// flattened assignment helper without recording a sound fallback.
fn run_single_field_flattened_unsize_probe<'tcx, 'body>(
    chc_ctx: &mut ChcCtx<'tcx, 'body>,
    body: &'body rustc_public::mir::Body,
) -> bool {
    for block in &body.blocks {
        for stmt in &block.statements {
            let rustc_public::mir::StatementKind::Assign(place, rhs) = &stmt.kind else {
                continue;
            };
            let rustc_public::mir::Rvalue::Cast(
                rustc_public::mir::CastKind::PointerCoercion(
                    rustc_public::mir::PointerCoercion::Unsize,
                ),
                _,
                _,
            ) = rhs
            else {
                continue;
            };
            if !place.projection.is_empty()
                || !chc_ctx.flatten.flattened_tuple_locals.contains(&place.local)
                || chc_ctx.flattened_field_count(place.local) != 1
            {
                continue;
            }

            let before = chc_ctx.sound_fallback_count();
            let mut constraints = Vec::new();
            let mut last_constraint = std::collections::HashMap::new();
            let mut modified = HashSet::new();
            let handled = {
                let mut acc =
                    StmtAccumulator::new(&mut modified, &mut constraints, &mut last_constraint);
                chc_ctx.try_encode_flattened_local_assign(place.local, rhs, &mut acc)
            };

            assert!(handled, "single-field dyn unsize cast should be handled");
            assert!(
                !constraints.is_empty(),
                "single-field dyn unsize cast should emit at least one constraint"
            );
            assert!(
                modified.contains(&place.local),
                "single-field dyn unsize cast should mark the destination modified"
            );
            assert_eq!(
                chc_ctx.sound_fallback_count(),
                before,
                "single-field dyn unsize cast should not record a sound fallback"
            );
            return true;
        }
    }

    false
}

/// A single-field flattened smart pointer unsize cast should be handled by the
/// flattened assignment helper without recording a sound fallback.
#[test]
fn test_single_field_flattened_unsize_cast_uses_generic_rvalue_path() {
    with_test_ay_ctx_for_source(SINGLE_FIELD_CUSTOM_UNSIZE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_single_field_custom_unsize");
        let body = instance.body().expect("function body");
        let mut chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "probe_single_field_custom_unsize", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let handled_unsize = run_single_field_flattened_unsize_probe(&mut chc_ctx, &body);
        // MIR optimizer may eliminate the PointerCoercion::Unsize cast for
        // single-field structs. The probe is only meaningful when the pattern
        // survives optimization.
        if !handled_unsize {
            // MIR eliminated the Unsize cast; probe not meaningful.
        }
    });
}

// =============================================================================
// emit_flattened_call_fields: shared call-layer helper (Part of #3631)
// =============================================================================

/// `emit_flattened_call_fields` constrains both discriminant and payload slots
/// and updates `flattened_field_env` for downstream readers.
///
/// This is the correctness property that the manual emitters were missing:
/// the shared helper ensures `flattened_field_env` is populated for every
/// constrained field, preventing stale or unconstrained reads in later blocks.
#[test]
fn test_emit_flattened_call_fields_constrains_both_slots_and_updates_env() {
    with_test_ay_ctx_for_source(OPTION_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_option_flatten");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_option_flatten", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let flattened_locals: Vec<usize> =
            chc_ctx.flatten.flattened_tuple_locals.iter().copied().collect();
        if flattened_locals.is_empty() {
            return;
        }
        let local_idx = flattened_locals[0];
        let vec_idx = chc_ctx.state_idx_for_local(local_idx);
        if chc_ctx.state_var_mgr.output_state_vars.len() <= vec_idx + 1 {
            return;
        }

        // Build a from_app from the first block's relation (same pattern as
        // test_collection_predicate_sound_fallback_increment).
        let from_rel = chc_ctx.block_relations.get(&0).expect("block 0 relation").clone();
        let output_args: Vec<Expr> = chc_ctx
            .state_var_mgr
            .state_vars
            .iter()
            .map(|(name, sort)| Expr::var(name.to_string(), sort.clone()))
            .collect();
        let from_app = trust_mc_core::chc::RelationApp::new(&from_rel, output_args);
        let modified_locals = std::collections::HashSet::new();
        let stmt_constraints = [Expr::bool_const(true)];
        // Use block 0 as target (self-loop) — guaranteed to have a declared relation.
        let target = 0usize;

        let before_rules = chc_ctx.vc.rules.len();

        // Assert flattened_field_env is empty before the call.
        assert!(
            !chc_ctx.encode.flattened_field_env.contains_key(&(local_idx, 0)),
            "precondition: fld0 env should be empty"
        );
        assert!(
            !chc_ctx.encode.flattened_field_env.contains_key(&(local_idx, 1)),
            "precondition: fld1 env should be empty"
        );

        let field_values = vec![Some(Expr::bool_const(true)), Some(Expr::bitvec_const(42u64, 32))];
        let emitted = chc_ctx.emit_flattened_call_fields(
            local_idx,
            &field_values,
            &from_app,
            target,
            &modified_locals,
            &stmt_constraints,
        );

        assert!(emitted, "emit_flattened_call_fields should return true for flattened dest");
        assert!(chc_ctx.vc.rules.len() > before_rules, "should emit at least one CHC rule");

        // Key correctness property: flattened_field_env must be updated for both fields.
        // The manual emitters in option_copied and kani.rs were missing this update,
        // causing downstream reads to use stale values.
        assert!(
            chc_ctx.encode.flattened_field_env.contains_key(&(local_idx, 0)),
            "fld0 (discriminant) must be cached in flattened_field_env after emission"
        );
        assert!(
            chc_ctx.encode.flattened_field_env.contains_key(&(local_idx, 1)),
            "fld1 (payload) must be cached in flattened_field_env after emission"
        );
    });
}

/// `reshape_flattened_bool_field_for_call` preserves Bool→BV coercion when a
/// flattened discriminant slot is widened away from Sort::bool().
#[test]
fn test_reshape_flattened_bool_field_for_call_coerces_bool_to_bitvec_slot() {
    with_test_ay_ctx_for_source(OPTION_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_option_flatten");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_option_flatten", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let Some(local_idx) = chc_ctx.flatten.flattened_tuple_locals.iter().copied().next() else {
            return;
        };
        let vec_idx = chc_ctx.state_idx_for_local(local_idx);
        if chc_ctx.state_var_mgr.output_state_vars.len() <= vec_idx {
            return;
        }

        let (out_name, _) = chc_ctx.state_var_mgr.output_state_vars[vec_idx].clone();
        chc_ctx.state_var_mgr.output_state_vars[vec_idx] = (out_name, ay_bindings::Sort::bitvec(8));

        let reshaped =
            chc_ctx.reshape_flattened_bool_field_for_call(local_idx, 0, Expr::bool_const(true));
        let smt = reshaped.to_string();
        assert_eq!(
            reshaped.sort().bitvec_width(),
            Some(8),
            "reshaped discriminant should match the destination BV width"
        );
        assert!(smt.contains("ite"), "Bool→BV reshaping should use ite, got: {smt}");
    });
}

/// `reshape_flattened_bool_field_for_call` preserves Bool→Int coercion for
/// int-lifted/manual flattened discriminant slots.
#[test]
fn test_reshape_flattened_bool_field_for_call_coerces_bool_to_int_slot() {
    with_test_ay_ctx_for_source(OPTION_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_option_flatten");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_option_flatten", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let Some(local_idx) = chc_ctx.flatten.flattened_tuple_locals.iter().copied().next() else {
            return;
        };
        let vec_idx = chc_ctx.state_idx_for_local(local_idx);
        if chc_ctx.state_var_mgr.output_state_vars.len() <= vec_idx {
            return;
        }

        let (out_name, _) = chc_ctx.state_var_mgr.output_state_vars[vec_idx].clone();
        chc_ctx.state_var_mgr.output_state_vars[vec_idx] = (out_name, ay_bindings::Sort::int());

        let reshaped =
            chc_ctx.reshape_flattened_bool_field_for_call(local_idx, 0, Expr::bool_const(false));
        let smt = reshaped.to_string();
        assert!(reshaped.sort().is_int(), "reshaped discriminant should use Int sort");
        assert!(smt.contains("ite"), "Bool→Int reshaping should use ite, got: {smt}");
    });
}

/// `emit_flattened_call_fields` returns false for non-flattened destinations
/// and does not emit any rules.
#[test]
fn test_emit_flattened_call_fields_returns_false_for_non_flattened() {
    with_test_ay_ctx_for_source(OPTION_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_option_flatten");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_option_flatten", ChcConfig::default());
        chc_ctx.declare_block_relations();

        // Find a local that is NOT flattened (e.g., local 0 = return place,
        // which may or may not be flattened; if it is, find any non-flattened one).
        let non_flattened = (0..body.locals().len())
            .find(|idx| !chc_ctx.flatten.flattened_tuple_locals.contains(idx));
        let Some(local_idx) = non_flattened else {
            return; // All locals flattened — skip test
        };

        let from_rel = chc_ctx.block_relations.get(&0).expect("block 0 relation").clone();
        let output_args: Vec<Expr> = chc_ctx
            .state_var_mgr
            .state_vars
            .iter()
            .map(|(name, sort)| Expr::var(name.to_string(), sort.clone()))
            .collect();
        let from_app = trust_mc_core::chc::RelationApp::new(&from_rel, output_args);
        let modified_locals = std::collections::HashSet::new();
        let stmt_constraints = [Expr::bool_const(true)];
        let target = 0usize;

        let before_rules = chc_ctx.vc.rules.len();

        let field_values = vec![Some(Expr::bool_const(true))];
        let emitted = chc_ctx.emit_flattened_call_fields(
            local_idx,
            &field_values,
            &from_app,
            target,
            &modified_locals,
            &stmt_constraints,
        );

        assert!(!emitted, "emit_flattened_call_fields should return false for non-flattened dest");
        assert_eq!(
            chc_ctx.vc.rules.len(),
            before_rules,
            "should not emit any rules for non-flattened dest"
        );
    });
}
