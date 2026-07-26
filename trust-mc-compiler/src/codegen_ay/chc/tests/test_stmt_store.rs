// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Tests for CHC codegen_stmt_store.rs — deref store, array element store,
//! and ref_targets-based store paths.
//!
//! Part of #2016 (test coverage for chc/codegen_stmt_store.rs, 652 lines).
//!
//! These are MIR-driven pipeline tests: compile Rust source with store patterns,
//! run ChcCtx::translate(), and verify the generated VC has correct structure.

#![allow(clippy::unwrap_used)]

use super::super::stmt_accumulator::StmtAccumulator;
use super::common::*;
use crate::codegen_ay::chc::codegen_ctx::diagnostics::ChcDiagnostics;
use crate::codegen_ay::emit_chc;

mod test_stmt_store_option_coerce;

// Removed: constraint_strings helper — replaced by streaming helpers in common.rs
// (any_constraint_str, count_constraint_str, has_any_constraints)

// =============================================================================
// Reg-level deref store via ref_targets (handle_deref_store_via_ref_targets)
// =============================================================================

/// Reg-level scalar deref store: *r = value where r is a mutable reference.
/// Exercises handle_deref_store_via_ref_targets → scalar path.
#[test]
fn test_reg_level_scalar_deref_store() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn scalar_store(r: &mut u32, val: u32) {
            *r = val;
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "scalar_store");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "scalar_store", ChcConfig::default());

        let (vc, _needs_mem_promote) = chc_ctx.translate();
        let smt = emit_chc(&vc).to_string();
        let transition_rule_count = vc.rules.iter().filter(|r| r.body.relation.is_some()).count();

        assert!(!smt.is_empty(), "Reg-level scalar deref store should produce non-empty VC");
        assert!(
            vc.rules.len() >= body.blocks.len(),
            "Should have at least one rule per BB, got {} rules for {} BBs",
            vc.rules.len(),
            body.blocks.len()
        );
        // Part of #3052: Return terminator now emits a self-transition rule
        // carrying statement constraints, so single-block functions have their
        // store constraints captured in the VC.
        assert!(
            transition_rule_count >= 1,
            "scalar_store should have at least 1 transition rule (return self-transition), got {transition_rule_count}"
        );
    });
}

/// Reg-level struct field deref store: (*r).field = value.
/// Exercises handle_deref_store_via_ref_targets → field projection path.
#[test]
fn test_reg_level_struct_field_deref_store() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub struct Point { pub x: u32, pub y: u32 }

        pub fn set_field(p: &mut Point, val: u32) {
            p.x = val;
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "set_field");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "set_field", ChcConfig::default());

        let (vc, _needs_mem_promote) = chc_ctx.translate();
        let smt = emit_chc(&vc).to_string();
        let transition_rule_count = vc.rules.iter().filter(|r| r.body.relation.is_some()).count();

        assert!(!smt.is_empty(), "Reg-level struct field deref store should produce non-empty VC");
        assert!(vc.rules.len() >= body.blocks.len(), "Should have at least one rule per BB");
        // Part of #3052: Return terminator self-transition captures store constraints.
        assert!(
            transition_rule_count >= 1,
            "set_field should have at least 1 transition rule (return self-transition), got {transition_rule_count}"
        );
    });
}

/// Multiple field writes to the same struct through the same reference.
/// Tests the last_constraint_for_local superseding logic.
#[test]
fn test_reg_level_multiple_field_writes() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub struct Point { pub x: u32, pub y: u32 }

        pub fn set_both(p: &mut Point) {
            p.x = 10;
            p.y = 20;
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "set_both");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "set_both", ChcConfig::default());

        let (vc, _needs_mem_promote) = chc_ctx.translate();
        let transition_rule_count = vc.rules.iter().filter(|r| r.body.relation.is_some()).count();
        assert!(!vc.rules.is_empty(), "Multiple field writes should produce rules");
        // Part of #3052: Return terminator self-transition captures store constraints.
        assert!(
            transition_rule_count >= 1,
            "set_both should have at least 1 transition rule (return self-transition), got {transition_rule_count}"
        );
    });
}

/// Directly unit-test the Reg-level ref-target store helper to ensure it emits
/// a concrete value-flow constraint (and not a passthrough equality).
///
/// After commit d358006 (auxiliary pointee state vars for &T/&mut T arg deref stores),
/// the constraint targets `_scalar_store_1_pointee__out` instead of `_scalar_store_1__out`
/// because &mut u32 arguments now get dedicated pointee state variables.
#[test]
fn test_reg_level_scalar_deref_store_helper_emits_specific_constraint_shape() {
    use rustc_public::mir::{Local, Place, ProjectionElem};
    use std::collections::HashMap;

    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn scalar_store(r: &mut u32, val: u32) {
            *r = val;
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "scalar_store");
        let body = instance.body().expect("function body");

        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "scalar_store", ChcConfig::default());
        chc_ctx.declare_block_relations();

        // local 1 (`r`) points to local 1's tracked value slot at Reg level.
        chc_ctx.ref_resolution.ref_targets.insert(1, RefTarget { local: 1, projections: vec![] });

        let rhs_vec_idx = *chc_ctx
            .state_var_mgr
            .local_to_state_idx
            .get(&2)
            .expect("expected tracked state index for `val` local");
        let (rhs_name, rhs_sort) = chc_ctx
            .state_var_mgr
            .state_vars
            .get(rhs_vec_idx)
            .expect("missing input state var for val local");
        let rhs_expr = Expr::var(rhs_name.to_string(), rhs_sort.clone());

        let lhs = Place { local: Local::from(1usize), projection: vec![ProjectionElem::Deref] };
        let mut modified = HashSet::new();
        let mut constraints = Vec::new();
        let mut last_constraint_for_local = HashMap::new();

        let handled = {
            let mut acc = StmtAccumulator::new(
                &mut modified,
                &mut constraints,
                &mut last_constraint_for_local,
            );
            chc_ctx.handle_deref_store_via_ref_targets(&lhs, rhs_expr, 1, &mut acc)
        };
        assert!(handled, "scalar deref store helper should handle *r = val");

        let constraint_strings: Vec<String> = constraints.iter().map(ToString::to_string).collect();
        // After auxiliary pointee vars, the output variable is _scalar_store_1_pointee__out
        assert!(
            constraint_strings.iter().any(
                |c| c.contains("_scalar_store_1_pointee__out") && c.contains("_scalar_store_2")
            ),
            "expected concrete value-flow equality from val input to pointee output, got {constraint_strings:?}"
        );
        assert!(
            !constraint_strings
                .iter()
                .any(|c| c.contains("(= _scalar_store_1_pointee__out _scalar_store_1_pointee__in)")),
            "regression: helper must not emit passthrough equality for the updated pointee local, got {constraint_strings:?}"
        );
    });
}

/// Directly unit-test arg-ref field deref helper path to ensure `(*arg).field = value`
/// emits a concrete pointee update constraint instead of silently dropping the store.
#[test]
fn test_reg_level_arg_field_deref_store_helper_emits_projection_update_constraint() {
    use rustc_public::mir::{Local, Place, ProjectionElem};
    use std::collections::HashMap;

    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub struct Pair { pub left: u32, pub right: u32 }

        pub fn field_store_arg(r: &mut Pair, val: u32) {
            r.left = val;
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "field_store_arg");
        let body = instance.body().expect("function body");

        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "field_store_arg", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let pointee_vec_idx = *chc_ctx
            .ref_resolution
            .ref_arg_pointee_idx
            .get(&1)
            .expect("expected arg-ref pointee slot for local 1");
        let track_key = usize::MAX - pointee_vec_idx;

        let rhs_vec_idx = *chc_ctx
            .state_var_mgr
            .local_to_state_idx
            .get(&2)
            .expect("expected tracked state index for `val` local");
        let (rhs_name, rhs_sort) = chc_ctx
            .state_var_mgr
            .state_vars
            .get(rhs_vec_idx)
            .expect("missing input state var for val local");
        let rhs_expr = Expr::var(rhs_name.to_string(), rhs_sort.clone());

        let field_ty = body.locals()[2].ty;
        let lhs = Place {
            local: Local::from(1usize),
            projection: vec![ProjectionElem::Deref, ProjectionElem::Field(0, field_ty)],
        };
        let mut modified = HashSet::new();
        let mut constraints = Vec::new();
        let mut last_constraint_for_local = HashMap::new();

        let handled = {
            let mut acc = StmtAccumulator::new(
                &mut modified,
                &mut constraints,
                &mut last_constraint_for_local,
            );
            chc_ctx.handle_deref_store_via_ref_targets(&lhs, rhs_expr, 1, &mut acc)
        };
        assert!(handled, "arg field deref store helper should handle (*r).field = val");

        let constraint_strings: Vec<String> = constraints.iter().map(ToString::to_string).collect();
        assert!(
            constraint_strings.iter().any(|c| {
                c.contains("_field_store_arg_1_pointee__out") && c.contains("_field_store_arg_2")
            }),
            "expected concrete field-update equality from val input to pointee output, got {constraint_strings:?}"
        );
        assert!(
            constraint_strings.iter().any(|c| c.contains("(fld_right _field_store_arg_1_pointee)")),
            "field update should preserve untouched field from pointee input, got {constraint_strings:?}"
        );
        assert!(
            !constraint_strings.iter().any(|c| c
                .contains("(= _field_store_arg_1_pointee__out _field_store_arg_1_pointee__in)")),
            "regression: helper must not emit passthrough equality for updated pointee, got {constraint_strings:?}"
        );
        assert!(
            chc_ctx.encode.modified_state_indices.contains(&pointee_vec_idx),
            "arg pointee slot should be marked modified"
        );
        assert!(
            last_constraint_for_local.contains_key(&track_key),
            "arg pointee track key should record the emitted constraint"
        );
    });
}

// =============================================================================
// Array element store (handle_array_element_store)
// =============================================================================

/// Simple array element store: arr[idx] = value at Reg level.
/// Exercises handle_array_element_store → Index projection path.
#[test]
fn test_reg_level_array_element_store() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn array_store(arr: &mut [u32; 4], idx: usize, val: u32) {
            arr[idx] = val;
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "array_store");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "array_store", ChcConfig::default());

        let (vc, _needs_mem_promote) = chc_ctx.translate();
        let smt = emit_chc(&vc).to_string();

        assert!(!smt.is_empty(), "Reg-level array element store should produce non-empty VC");
        assert!(vc.rules.len() >= body.blocks.len(), "Should have at least one rule per BB");
        // Semantic: array element store generates store() in SMT Array theory.
        assert!(
            smt.contains("store"),
            "Array element store should use SMT store() operation, got: {}",
            &smt[..smt.len().min(500)]
        );
    });
}

/// Mem-level deref store exercises handle_deref_store_mem_level.
/// Uses a Mem track level to specifically exercise the memory-level deref code path.
#[test]
fn test_mem_level_deref_store_code_path() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn mem_store(ptr: &mut u32) {
            *ptr = 42;
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "mem_store");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            "mem_store",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );

        let (vc, _needs_mem_promote) = chc_ctx.translate();
        let smt = emit_chc(&vc).to_string();

        assert!(!smt.is_empty(), "Mem-level deref store should produce non-empty VC");
        assert!(
            smt.contains("declare-rel") || smt.contains("declare-fun"),
            "Mem-level store VC should declare block relations"
        );
        // Semantic: Mem-level deref store writes to the heap memory array.
        // Should use store() to update the memory array.
        assert!(
            smt.contains("store"),
            "Mem-level deref store should use store() for memory write, got: {}",
            &smt[..smt.len().min(500)]
        );
        // The constant 42 should appear in the SMT output.
        assert!(
            smt.contains("42") || smt.contains("#x0000002a"),
            "Mem-level store of 42 should include the constant value"
        );
    });
}

/// Mem-level safe-ref store should mirror into register state in addition to
/// heap memory. This preserves `*ptr = v; *ptr` round-trip semantics.
#[test]
fn test_mem_level_safe_ref_store_emits_register_mirror() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn mem_store_roundtrip() -> u32 {
            let mut x: u32 = 0;
            let ptr = &mut x;
            *ptr = 42;
            *ptr
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "mem_store_roundtrip");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            "mem_store_roundtrip",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );

        let (vc, _needs_mem_promote) = chc_ctx.translate();
        let smt = emit_chc(&vc).to_string();
        assert!(!vc.rules.is_empty(), "Mem-level roundtrip store should produce rules");

        // After ay bump to declare-var encoding, state variables are declared
        // as free variables rather than relation arguments. Constraint expressions
        // may appear in body constraints, head args, or be implicit via declared
        // variable equalities. Check the semantic invariants:
        // 1. Heap memory is modeled (Array-sorted vars or store() in constraints)
        let has_memory_model = any_constraint_str(&vc, |c| c.contains("(store "))
            || smt.contains("(store ")
            || vc.vars().iter().any(|v| v.sort.is_array() && v.name.contains("mem"));
        assert!(
            has_memory_model,
            "Mem-level safe-ref store should model heap memory, got: {}",
            &smt[..smt.len().min(700)]
        );

        // 2. Register mirror: the constant 42 (0x2A) should appear in the VC
        //    and the output variable for local 1 should be referenced.
        let has_register_mirror = any_constraint_str(&vc, |c| {
            c.contains("_mem_store_roundtrip_1__out") && c.contains("#x0000002a")
        }) || (smt.contains("_mem_store_roundtrip_1__out")
            && smt.contains("#x0000002a"));
        assert!(
            has_register_mirror,
            "Mem-level safe-ref store should emit register mirror equality for pointee local, got: {}",
            &smt[..smt.len().min(900)]
        );
    });
}

/// Mem-level field write through a safe reference should also mirror the updated
/// aggregate into register state so subsequent deref reads see the field mutation.
#[test]
fn test_mem_level_safe_ref_field_store_emits_register_mirror() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub struct Pair { pub a: u32, pub b: u32 }

        pub fn mem_field_store_roundtrip() -> u32 {
            let mut p = Pair { a: 0, b: 7 };
            let ptr = &mut p;
            (*ptr).a = 99;
            (*ptr).a
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "mem_field_store_roundtrip");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            "mem_field_store_roundtrip",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );

        let (vc, _needs_mem_promote) = chc_ctx.translate();
        let smt = emit_chc(&vc).to_string();
        assert!(!vc.rules.is_empty(), "Mem-level ref field store should produce rules");

        // After ay bump to declare-var encoding, state variables are free
        // variables. Check semantic invariants rather than specific encoding form.
        let has_memory_model = any_constraint_str(&vc, |c| c.contains("(store "))
            || smt.contains("(store ")
            || vc.vars().iter().any(|v| v.sort.is_array() && v.name.contains("mem"));
        assert!(
            has_memory_model,
            "Mem-level safe-ref field store should model heap memory, got: {}",
            &smt[..smt.len().min(700)]
        );

        let has_register_mirror = any_constraint_str(&vc, |c| {
            c.contains("_mem_field_store_roundtrip_1_fld0__out") && c.contains("#x00000063")
        }) || (smt.contains("_mem_field_store_roundtrip_1_fld0__out")
            && smt.contains("#x00000063"));
        assert!(
            has_register_mirror,
            "Mem-level safe-ref field store should emit register mirror equality, got: {}",
            &smt[..smt.len().min(900)]
        );
    });
}

/// Symbolic `copy_nonoverlapping` should update destination array state at Reg level.
///
/// Regression for ignored `StatementKind::Intrinsic(CopyNonOverlapping)` in CHC
/// statement encoding: destination `__out` must be constrained by a guarded store chain.
#[test]
fn test_reg_level_copy_nonoverlapping_symbolic_updates_dst_u8() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        use std::ptr;

        pub fn probe_copy_dynamic(mut dst: [u8; 4], src: [u8; 4], count: usize) -> [u8; 4] {
            unsafe {
                ptr::copy_nonoverlapping(src.as_ptr(), dst.as_mut_ptr(), count);
            }
            dst
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_copy_dynamic");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_copy_dynamic", ChcConfig::default());
        let (vc, _needs_mem_promote) = chc_ctx.translate();
        let smt = emit_chc(&vc).to_string();

        assert!(
            smt.contains("(= _probe_copy_dynamic_1__out"),
            "copy_nonoverlapping should constrain dst __out variable, got: {}",
            &smt[..smt.len().min(1000)]
        );
        assert!(
            smt.contains("(store"),
            "copy_nonoverlapping should encode array updates with store(), got: {}",
            &smt[..smt.len().min(1000)]
        );
        assert!(
            smt.contains("(ite"),
            "symbolic count copy should be guarded with ite(count), got: {}",
            &smt[..smt.len().min(1000)]
        );
    });
}

/// Bool arrays should also be updated for symbolic `copy_nonoverlapping`.
#[test]
fn test_reg_level_copy_nonoverlapping_symbolic_updates_dst_bool() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        use std::ptr;

        pub fn probe_copy_dynamic_bool(
            mut dst: [bool; 4],
            src: [bool; 4],
            count: usize,
        ) -> [bool; 4] {
            unsafe {
                ptr::copy_nonoverlapping(src.as_ptr(), dst.as_mut_ptr(), count);
            }
            dst
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_copy_dynamic_bool");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_copy_dynamic_bool", ChcConfig::default());
        let (vc, _needs_mem_promote) = chc_ctx.translate();
        let smt = emit_chc(&vc).to_string();

        assert!(
            smt.contains("(= _probe_copy_dynamic_bool_1__out"),
            "copy_nonoverlapping should constrain bool dst __out variable, got: {}",
            &smt[..smt.len().min(1000)]
        );
        assert!(
            smt.contains("(store"),
            "bool copy_nonoverlapping should encode array updates with store(), got: {}",
            &smt[..smt.len().min(1000)]
        );
        assert!(
            smt.contains("(ite"),
            "symbolic bool copy should be guarded with ite(count), got: {}",
            &smt[..smt.len().min(1000)]
        );
    });
}

/// Mem-level struct field write through pointer exercises handle_deref_store_mem_level
/// with Field projections after Deref.
#[test]
fn test_mem_level_deref_field_store() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub struct Pair { pub a: u32, pub b: u32 }

        pub fn write_field(p: &mut Pair) {
            p.a = 99;
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "write_field");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            "write_field",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );

        let (vc, _needs_mem_promote) = chc_ctx.translate();
        let smt = emit_chc(&vc).to_string();
        assert!(!vc.rules.is_empty(), "Mem-level struct field deref store should produce rules");
        // Semantic: Mem-level field store should use store() for memory write
        // and the constant 99 should appear.
        assert!(
            smt.contains("store"),
            "Mem-level field store should use store(), got: {}",
            &smt[..smt.len().min(500)]
        );
        assert!(
            smt.contains("99") || smt.contains("#x00000063"),
            "Mem-level field store of 99 should include the constant value"
        );
    });
}

// =============================================================================
// Ref_target array store (handle_deref_store_array_via_ref_targets, emit_ref_target_array_update)
// =============================================================================

/// Write through ref to mutable Vec element — exercises the ref_targets path.
/// When the ref points to an array element (arr[idx]), the store should
/// update both the ref target and the array state.
#[test]
fn test_reg_level_ref_target_array_store_pattern() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn ref_array_element(arr: &mut [u32; 3]) {
            let x = &mut arr[0];
            *x = 100;
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "ref_array_element");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "ref_array_element", ChcConfig::default());

        let (vc, _needs_mem_promote) = chc_ctx.translate();
        assert!(!vc.rules.is_empty(), "Reg-level ref→array store should produce rules");
        // Assert specific guard constraints emitted for the array-index branch.
        assert!(
            any_constraint_str(&vc, |c| c
                .contains("(= _ref_array_element_3__out #x0000000000000000)")),
            "ref_array_element should carry concrete zero index into _3__out"
        );
        assert!(
            any_constraint_str(&vc, |c| c.contains(
                "(= _ref_array_element_4__out (bvult #x0000000000000000 #x0000000000000003))"
            )),
            "ref_array_element should encode bounds check into _4__out"
        );
    });
}

// =============================================================================
// Mem-level with non-bitvec pointer sort (guard path in handle_deref_store_mem_level)
// =============================================================================

/// BigInt-like operations where pointer-like locals may have non-BV sort.
/// The guard at line 114 in codegen_stmt_store.rs should skip these.
#[test]
fn test_mem_level_arithmetic_no_deref() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn simple_arith(x: u64, y: u64) -> u64 {
            x.wrapping_add(y)
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "simple_arith");
        let body = instance.body().expect("function body");

        // Even at Mem level, pure arithmetic should produce valid VC
        let chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            "simple_arith",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );

        let (vc, _needs_mem_promote) = chc_ctx.translate();
        let smt = emit_chc(&vc).to_string();
        assert!(!vc.rules.is_empty(), "Pure arithmetic at Mem-level should still produce rules");
        // Semantic: wrapping_add should produce bvadd in the SMT output.
        assert!(
            smt.contains("bvadd"),
            "wrapping_add should produce bvadd in SMT, got: {}",
            &smt[..smt.len().min(500)]
        );
    });
}

// =============================================================================
// Track level comparison — Reg vs Mem produce different VCs
// =============================================================================

/// Same source at Reg and Mem levels should both produce rules,
/// but Mem-level may produce different constraint structure.
#[test]
fn test_track_level_comparison_for_deref_store() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn assign_ref(r: &mut u32, v: u32) {
            *r = v;
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "assign_ref");
        let body = instance.body().expect("function body");

        // Reg level
        let chc_ctx_reg = ChcCtx::new(ctx.tcx, &body, "assign_ref", ChcConfig::default());
        let (vc_reg, _) = chc_ctx_reg.translate();

        // Mem level
        let chc_ctx_mem = ChcCtx::new(
            ctx.tcx,
            &body,
            "assign_ref",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );
        let (vc_mem, _) = chc_ctx_mem.translate();

        // Both should produce non-empty VCs
        assert!(!vc_reg.rules.is_empty(), "Reg-level VC should have rules");
        assert!(!vc_mem.rules.is_empty(), "Mem-level VC should have rules");

        // Mem level should have at least as many variables (memory state variables)
        let smt_reg = emit_chc(&vc_reg).to_string();
        let smt_mem = emit_chc(&vc_mem).to_string();
        assert!(!smt_reg.is_empty(), "Reg-level SMT should be non-empty");
        assert!(!smt_mem.is_empty(), "Mem-level SMT should be non-empty");
        // Semantic: Mem-level deref store should use store() for heap memory writes,
        // while Reg-level inlines through ref_targets and uses equality.
        assert!(
            smt_mem.contains("store"),
            "Mem-level deref store should use store() for memory writes, got: {}",
            &smt_mem[..smt_mem.len().min(500)]
        );
    });
}

// =============================================================================
// Constant index store (ConstantIndex projection path)
// =============================================================================

/// Constant index array access exercises the ConstantIndex branch
/// in handle_array_element_store.
#[test]
fn test_reg_level_constant_index_store() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn set_first(arr: &mut [u32; 4]) {
            arr[0] = 42;
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "set_first");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "set_first", ChcConfig::default());

        let (vc, _needs_mem_promote) = chc_ctx.translate();
        assert!(!vc.rules.is_empty(), "Constant index store should produce rules");
        // Assert concrete guard/index constraints (rather than generic '=' tokens).
        assert!(
            any_constraint_str(&vc, |c| c.contains("(= _set_first_2__out #x0000000000000000)")),
            "set_first should carry concrete zero index into _2__out"
        );
        assert!(
            any_constraint_str(&vc, |c| c
                .contains("(= _set_first_3__out (bvult #x0000000000000000 #x0000000000000004))")),
            "set_first should encode bounds check into _3__out"
        );
    });
}

/// Multiple sequential array writes to different indices.
#[test]
fn test_reg_level_multiple_array_writes() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn init_pair(arr: &mut [u32; 4]) {
            arr[0] = 10;
            arr[1] = 20;
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "init_pair");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "init_pair", ChcConfig::default());

        let (vc, _needs_mem_promote) = chc_ctx.translate();
        let smt = emit_chc(&vc).to_string();
        assert!(!vc.rules.is_empty(), "Multiple array writes should produce rules");
        // Semantic: two sequential array writes to different indices should
        // produce block relations and multiple state variables for the array elements.
        assert!(
            smt.contains("init_pair__bb"),
            "Multiple array writes should produce block relations"
        );
        // Two writes produce at least 2 distinct constraints.
        assert!(
            vc.rules.len() >= 2,
            "Multiple array writes should produce at least 2 rules, got {}",
            vc.rules.len()
        );
    });
}

// =============================================================================
// Nested struct access at Mem level (Deref + Field + Field)
// =============================================================================

/// Nested struct field write at Mem level.
/// Exercises the multi-projection path in handle_deref_store_mem_level.
#[test]
fn test_mem_level_nested_struct_field_write() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub struct Inner { pub val: u32 }
        pub struct Outer { pub inner: Inner }

        pub fn set_nested(o: &mut Outer, v: u32) {
            o.inner.val = v;
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "set_nested");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            "set_nested",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );

        let (vc, _needs_mem_promote) = chc_ctx.translate();
        let smt = emit_chc(&vc).to_string();
        assert!(
            !vc.rules.is_empty(),
            "Nested struct field write at Mem-level should produce rules"
        );
        // Semantic: Mem-level nested struct store should use store() for heap writes
        // and reference struct type names (Inner, Outer, or field accessors).
        assert!(
            smt.contains("store"),
            "Mem-level nested struct store should use store(), got: {}",
            &smt[..smt.len().min(500)]
        );
    });
}

// =============================================================================
// Dropped store counter (Part of #2236)
// =============================================================================

/// Missing output state vars in the ref-target array store path should be
/// diagnosed as dropped stores (not silently fall through).
#[test]
fn test_ref_target_array_store_missing_output_var_counts_drop() {
    use std::collections::HashMap;

    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn ref_target_drop_probe(x: u32) -> u32 {
            x
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "ref_target_drop_probe");
        let body = instance.body().expect("function body");
        let mut chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "ref_target_drop_probe", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let target_local = *chc_ctx
            .state_var_mgr
            .local_to_state_idx
            .keys()
            .next()
            .expect("expected at least one state local");
        let idx_local = target_local;
        let ref_local = target_local + 10_000;
        chc_ctx.ref_resolution.ref_targets.insert(
            ref_local,
            RefTarget::with_projections(target_local, vec![ProjectionElem::Index(idx_local)]),
        );

        // Force arr_out lookup failure inside handle_deref_store_array_via_ref_targets.
        chc_ctx.state_var_mgr.output_state_vars.clear();

        let lhs = Place { local: ref_local, projection: vec![ProjectionElem::Deref] };
        let rhs_expr = Expr::bitvec_const(100u128, POINTER_WIDTH);
        let mut modified = HashSet::new();
        let mut constraints = Vec::new();
        let mut last_constraint_for_local = HashMap::new();

        let handled = {
            let mut acc = StmtAccumulator::new(
                &mut modified,
                &mut constraints,
                &mut last_constraint_for_local,
            );
            chc_ctx.handle_deref_store_via_ref_targets(&lhs, rhs_expr, ref_local, &mut acc)
        };

        assert!(
            handled,
            "Missing ref-target output var should be treated as a handled dropped store"
        );
        assert!(
            chc_ctx.diagnostics.store_dropped_transition.get() > 0,
            "Missing ref-target output var should increment dropped-store counter"
        );
    });
}

// =============================================================================
// coerce_store_value — Sort coercion for array store values
// Part of #2244: array .store() asserts value sort matches element sort
// =============================================================================

fn take_pending_fresh_var_decls() -> Vec<trust_mc_core::chc::VarDecl> {
    PENDING_FRESH_VAR_DECLS.with(|decls| std::mem::take(&mut *decls.borrow_mut()))
}

/// Same sort — no coercion needed, value returned unchanged.
#[test]
fn test_coerce_store_value_same_sort_noop() {
    let arr_sort = Sort::array(Sort::bitvec(POINTER_WIDTH), Sort::bitvec(32));
    let value = Expr::bitvec_const(42u64, 32);
    let diagnostics = ChcDiagnostics::default();
    let result = ChcCtx::coerce_store_value(&arr_sort, value, false, &diagnostics);
    assert_eq!(*result.sort(), Sort::bitvec(32), "same-sort value should pass through unchanged");
}

/// BV width mismatch: BV8 value stored into Array<_, BV32> → widen to BV32.
#[test]
fn test_coerce_store_value_bv_width_narrow_to_wide() {
    let arr_sort = Sort::array(Sort::bitvec(POINTER_WIDTH), Sort::bitvec(32));
    let value = Expr::bitvec_const(1u64, 8);
    let diagnostics = ChcDiagnostics::default();
    let result = ChcCtx::coerce_store_value(&arr_sort, value, false, &diagnostics);
    assert_eq!(
        result.sort().bitvec_width(),
        Some(32),
        "BV8 stored into BV32 array should be widened to BV32"
    );
}

/// BV width mismatch: BV64 value stored into Array<_, BV32> → truncate to BV32.
#[test]
fn test_coerce_store_value_bv_width_wide_to_narrow() {
    let arr_sort = Sort::array(Sort::bitvec(POINTER_WIDTH), Sort::bitvec(32));
    let value = Expr::bitvec_const(1u64, 64);
    let diagnostics = ChcDiagnostics::default();
    let result = ChcCtx::coerce_store_value(&arr_sort, value, false, &diagnostics);
    assert_eq!(
        result.sort().bitvec_width(),
        Some(32),
        "BV64 stored into BV32 array should be truncated to BV32"
    );
}

/// Bool → BV: Bool value stored into Array<_, BV8> → ite(val, 1, 0) as BV8.
#[test]
fn test_coerce_store_value_bool_to_bv8() {
    let arr_sort = Sort::array(Sort::bitvec(POINTER_WIDTH), Sort::bitvec(8));
    let value = Expr::bool_const(true);
    let diagnostics = ChcDiagnostics::default();
    let result = ChcCtx::coerce_store_value(&arr_sort, value, false, &diagnostics);
    assert!(result.sort().is_bitvec(), "Bool stored into BV8 array should be coerced to bitvec");
    assert_eq!(
        result.sort().bitvec_width(),
        Some(8),
        "Bool stored into BV8 array should produce BV8"
    );
}

/// Bool → BV32: Bool value stored into Array<_, BV32>.
#[test]
fn test_coerce_store_value_bool_to_bv32() {
    let arr_sort = Sort::array(Sort::bitvec(POINTER_WIDTH), Sort::bitvec(32));
    let value = Expr::bool_const(false);
    let diagnostics = ChcDiagnostics::default();
    let result = ChcCtx::coerce_store_value(&arr_sort, value, false, &diagnostics);
    assert_eq!(
        result.sort().bitvec_width(),
        Some(32),
        "Bool stored into BV32 array should produce BV32"
    );
}

/// BV → Bool: BV1 value stored into Array<_, Bool> → val != 0.
#[test]
fn test_coerce_store_value_bv1_to_bool() {
    let arr_sort = Sort::array(Sort::bitvec(POINTER_WIDTH), Sort::bool());
    let value = Expr::bitvec_const(1u64, 1);
    let diagnostics = ChcDiagnostics::default();
    let result = ChcCtx::coerce_store_value(&arr_sort, value, false, &diagnostics);
    assert!(result.sort().is_bool(), "BV1 stored into Bool array should be coerced to Bool");
}

/// BV → Bool: BV8 value stored into Array<_, Bool> → val != 0.
#[test]
fn test_coerce_store_value_bv8_to_bool() {
    let arr_sort = Sort::array(Sort::bitvec(POINTER_WIDTH), Sort::bool());
    let value = Expr::bitvec_const(0u64, 8);
    let diagnostics = ChcDiagnostics::default();
    let result = ChcCtx::coerce_store_value(&arr_sort, value, false, &diagnostics);
    assert!(result.sort().is_bool(), "BV8 stored into Bool array should be coerced to Bool");
}

/// Non-array sort: value should pass through unchanged.
#[test]
fn test_coerce_store_value_non_array_sort_passthrough() {
    let non_array_sort = Sort::bitvec(32);
    let value = Expr::bitvec_const(42u64, 32);
    let diagnostics = ChcDiagnostics::default();
    let result = ChcCtx::coerce_store_value(&non_array_sort, value, false, &diagnostics);
    assert_eq!(
        *result.sort(),
        Sort::bitvec(32),
        "non-array sort should pass value through unchanged"
    );
}

/// Int value into BV array: coerced via int2bv since #2875 (committed eac0b55).
/// Before #2875, this fell through to fresh-symbolic substitution; now the
/// Int→BV coercion path handles it precisely without dropping the value.
#[test]
fn test_coerce_store_value_int_to_bv_uses_int2bv() {
    let _ = take_pending_fresh_var_decls();
    let arr_sort = Sort::array(Sort::bitvec(POINTER_WIDTH), Sort::bitvec(32));
    let value = Expr::int_const(42);
    let diagnostics = ChcDiagnostics::default();
    let result = ChcCtx::coerce_store_value(&arr_sort, value, false, &diagnostics);
    // Int→BV uses int2bv — per-ctx counter must NOT increment (no value dropped).
    assert_eq!(
        diagnostics.store_dropped_transition.get(),
        0,
        "Int→BV coercion via int2bv should not increment store_dropped_transition"
    );
    assert!(
        result.sort().is_bitvec() && result.sort().bitvec_width() == Some(32),
        "Int value into BV32 array should be coerced to BV32 (Part of #2875)"
    );
    // Verify the result is an int2bv conversion, not a fresh symbolic.
    assert!(
        matches!(result.value(), ExprValue::Int2Bv(_, 32)),
        "expected Int2Bv coercion, got {:?}",
        result.value()
    );
    // No pending declarations should be generated (no fresh symbolic created).
    let pending = take_pending_fresh_var_decls();
    assert!(
        pending.is_empty(),
        "int2bv coercion should not generate pending var declarations, got: {:?}",
        pending.iter().map(|decl| (&decl.name, &decl.sort)).collect::<Vec<_>>()
    );
}

/// Part of #3055: BV→Int unsigned uses bv2int (bare Bv2Int, no ITE sign-extension).
#[test]
fn test_coerce_store_value_bv_to_int_unsigned() {
    let _ = take_pending_fresh_var_decls();
    let arr_sort = Sort::array(Sort::bitvec(POINTER_WIDTH), Sort::int());
    let value = Expr::var("u32_val", Sort::bv32());
    let diagnostics = ChcDiagnostics::default();
    let result = ChcCtx::coerce_store_value(&arr_sort, value, false, &diagnostics);
    assert!(result.sort().is_int(), "BV32→Int coercion should produce Int sort");
    // Unsigned bv2int produces a bare Bv2Int node (no ITE sign-extension).
    assert!(
        !format!("{:?}", result).contains("Ite"),
        "unsigned bv2int should NOT produce ITE sign-extension, got {:?}",
        result
    );
}

/// Part of #3055: BV→Int signed uses bv2int_signed (ITE for two's complement).
#[test]
fn test_coerce_store_value_bv_to_int_signed() {
    let _ = take_pending_fresh_var_decls();
    let arr_sort = Sort::array(Sort::bitvec(POINTER_WIDTH), Sort::int());
    let value = Expr::var("i32_val", Sort::bv32());
    let diagnostics = ChcDiagnostics::default();
    let result = ChcCtx::coerce_store_value(&arr_sort, value, true, &diagnostics);
    assert!(result.sort().is_int(), "BV32→Int signed coercion should produce Int sort");
    // Signed bv2int_signed expands to ITE(msb==1, bv2int-2^width, bv2int).
    assert!(
        format!("{:?}", result).contains("Ite"),
        "signed bv2int should produce ITE sign-extension, got {:?}",
        result
    );
}

/// Datatype value into BV array: should be coerced to fresh symbolic of the
/// target element sort (Part of #2244). This is the primary sort mismatch
/// pattern — ADT values (Result, Closure, etc.) stored into BV-sorted
/// type-indexed memory arrays.
/// Part of #3099: fresh symbolic substitution is a sound over-approximation
/// (store emitted with universally-quantified value), so the demotion counter
/// must NOT increment — the encoding can never produce false proofs.
#[test]
fn test_coerce_store_value_datatype_to_bv_substitutes_fresh_symbolic() {
    let _ = take_pending_fresh_var_decls();
    let arr_sort = Sort::array(Sort::bitvec(POINTER_WIDTH), Sort::bitvec(32));
    // Create a Datatype value (Option-like enum with None/Some)
    let dt_sort =
        enum_sort("TestOption", [("None", vec![]), ("Some", vec![("fld_0", Sort::bitvec(32))])]);
    let value = Expr::var("_dt_val", dt_sort);
    assert!(value.sort().is_datatype(), "precondition: value should be Datatype");
    let diagnostics = ChcDiagnostics::default();
    let result = ChcCtx::coerce_store_value(&arr_sort, value, false, &diagnostics);
    // Part of #3099: the fresh symbolic path is a sound over-approximation.
    // The store IS emitted (store(arr, addr, fresh_sym)) with fresh_sym universally
    // quantified in the CHC rule. The solver proves for ALL possible values, which
    // is strictly stronger than the actual program. No demotion needed.
    assert_eq!(
        diagnostics.store_dropped_transition.get(),
        0,
        "coerce_store_value must NOT increment store_dropped_transition for fresh \
         symbolic substitution — this is a sound over-approximation (Part of #3099)"
    );
    assert!(
        result.sort().is_bitvec() && result.sort().bitvec_width() == Some(32),
        "Datatype value into BV32 array should be coerced to BV32 fresh symbolic (Part of #2244)"
    );
}

#[test]
fn test_coerce_store_value_single_field_datatype_to_bv_unwraps() {
    let arr_sort = Sort::array(Sort::bitvec(POINTER_WIDTH), Sort::bitvec(32));
    let tuple_sort = struct_sort("Tuple_bv32", [("fld_0", Sort::bitvec(32))]);
    let value = Expr::var("_tuple", tuple_sort);

    let diagnostics = ChcDiagnostics::default();
    let result = ChcCtx::coerce_store_value(&arr_sort, value.clone(), false, &diagnostics);
    let expected = value.field_select("Tuple_bv32", "fld_0", Sort::bitvec(32));

    assert_eq!(
        result, expected,
        "single-field datatype store value should unwrap to array element sort"
    );
}

// =============================================================================
// try_decompose_struct_store — Whole-struct deref store decomposition
// Bug 3a (#1739): decompose `*ptr = struct_val` into per-field memory stores
// Part of #2529
// =============================================================================

/// Whole-struct deref store at Mem level via function call return:
/// `*p = make_pair(a, b)`. Exercises try_decompose_struct_store path.
///
/// Direct struct literal `*p = Pair { x: a, y: b }` is lowered by MIR into
/// per-field stores, which bypasses try_decompose_struct_store. A function
/// call returning a struct produces a whole-struct Assign RHS that reaches
/// the decomposition path at Mem level.
#[test]
fn test_mem_level_struct_from_call_deref_store() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub struct Pair { pub x: u32, pub y: u32 }

        #[inline(never)]
        fn make_pair(a: u32, b: u32) -> Pair {
            Pair { x: a, y: b }
        }

        pub fn store_via_call(p: &mut Pair, a: u32, b: u32) {
            *p = make_pair(a, b);
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "store_via_call");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            "store_via_call",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );

        let (vc, _needs_mem_promote) = chc_ctx.translate();
        let smt = emit_chc(&vc).to_string();

        assert!(!vc.rules.is_empty(), "Struct-from-call deref store should produce rules");

        // At Mem level, the call destination write goes through the deref store path.
        // Depending on MIR lowering, this may produce store() for per-field decomposition,
        // or it may fall through to the standard memory store path.
        // Either way, the SMT should be non-empty and the pipeline should not crash.
        assert!(
            !smt.is_empty(),
            "Mem-level struct-from-call deref store should produce non-empty SMT"
        );

        // If try_decompose_struct_store fires, we'll see field_select or store.
        // If not, the standard path handles it. Both are valid — this test ensures
        // the pipeline processes whole-struct deref stores without error.
        let has_store = any_constraint_str(&vc, |c| c.contains("(store "));
        let has_alloc =
            any_constraint_str(&vc, |c| c.contains("obj_valid") || c.contains("obj_size"));
        assert!(
            has_store || has_alloc,
            "Pipeline should produce either store constraints or allocation tracking"
        );
    });
}

/// Tuple deref store at Mem level: `*ptr = (a, b)`.
/// Tuples use Aggregate rvalue which produces a whole-struct RHS, exercising
/// try_decompose_struct_store via the TyKind::RigidTy(Tuple) branch.
#[test]
fn test_mem_level_tuple_deref_store_decomposes() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn write_tuple(p: &mut (u32, u32), a: u32, b: u32) {
            *p = (a, b);
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "write_tuple");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            "write_tuple",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );

        let (vc, _needs_mem_promote) = chc_ctx.translate();

        assert!(!vc.rules.is_empty(), "Tuple deref store should produce rules");

        // Tuple (u32, u32) should decompose into 2 per-field stores.
        let store_count = count_constraint_str(&vc, |c| c.contains("(store "));
        assert!(
            store_count >= 2,
            "Tuple deref store should produce >= 2 store constraints (one per element), got {store_count}"
        );
    });
}
