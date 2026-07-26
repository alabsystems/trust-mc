// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Tests for `codegen_stmt_store_ref.rs` — Reg-level deref store via ref_targets (#1957).
//!
//! Part of #2303 (codegen_stmt_store_ref.rs, 342 LOC, zero dedicated coverage).
//! Covers:
//! - `handle_deref_store_via_ref_targets`: *ref = value at Reg level via ref_targets
//!   - Scalar path: *r = value → target_out = value
//!   - Field path: (*r).field = value → functional struct update
//!   - Missing output state var diagnostic (#2236)
//! - `handle_deref_store_array_via_ref_targets`: array element case for ref_target stores
//!   - Index and ConstantIndex projection paths
//!   - Array element field update (arr[idx].field = value)
//!   - Sort coercion at store boundaries (#2244)

// Test code: unwrap/panic are acceptable for assertions
#![allow(clippy::unwrap_used, clippy::panic)]

use super::super::stmt_accumulator::StmtAccumulator;
use super::common::*;

// Removed: constraint_texts helper — replaced by streaming helpers in common.rs
// (any_constraint_str, count_constraint_str, has_any_constraints)

/// Build an input state-variable expression for a MIR local.
fn state_var_expr_for_local(
    chc_ctx: &super::super::codegen_ctx::ChcCtx<'_, '_>,
    local: usize,
) -> ay_bindings::Expr {
    let idx = *chc_ctx.state_var_mgr.local_to_state_idx.get(&local).expect("tracked local");
    let (name, sort) = chc_ctx.state_var_mgr.state_vars.get(idx).expect("state var");
    ay_bindings::Expr::var(name.to_string(), sort.clone())
}

// =============================================================================
// Scalar deref store via ref_targets
// =============================================================================

const SCALAR_DEREF_STORE_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub fn write_via_ref(x: &mut u32, val: u32) {
        *x = val;
    }
"#;

/// Scalar *ref = value at Reg level: verifies ref_target seeding and constraint generation.
///
/// Part of #2496: `write_via_ref(*x = val)` at Reg level must create a pointee
/// state variable for the `&mut u32` argument and produce a VC that declares
/// __out variables for the pointee. Single-block functions (Return terminator)
/// have no successor → zero transition rules by design. The key verification is
/// that the pointee var exists in the VC and that non-trivial rules reference it.
#[test]
fn test_scalar_deref_store_via_ref_targets_reg_level() {
    with_test_ay_ctx_for_source(SCALAR_DEREF_STORE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "write_via_ref");
        let body = instance.body().expect("body");
        let vc = mir_to_chc(ctx.tcx, &body, "write_via_ref", ChcConfig::default());

        // Basic structure check
        assert!(!vc.rules.is_empty(), "should produce at least one rule");
        assert!(!vc.relations.is_empty(), "should produce at least one relation");

        // #2496: VC must declare a pointee variable for the &mut u32 argument
        let has_pointee_var = vc.vars().iter().any(|v| v.name.contains("_pointee"));
        assert!(
            has_pointee_var,
            "VC should declare a _pointee state variable for &mut argument (#2496)"
        );

        // The pointee __out variable must also exist
        let has_pointee_out =
            vc.vars().iter().any(|v| v.name.contains("_pointee") && v.name.contains("__out"));
        assert!(has_pointee_out, "VC should declare a _pointee__out variable (#2496)");
    });
}

/// Multi-block deref store produces transition rules with __out variables.
///
/// Part of #2496: Uses a function with branches (checked add creates Assert
/// terminator → multiple basic blocks) to verify that deref store constraints
/// flow through transition rules.
const MULTI_BLOCK_DEREF_STORE_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub fn write_sum_via_ref(x: &mut u32, a: u32, b: u32) {
        let sum = a + b;
        *x = sum;
    }
"#;

#[test]
fn test_multi_block_deref_store_produces_transition_rules() {
    with_test_ay_ctx_for_source(MULTI_BLOCK_DEREF_STORE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "write_sum_via_ref");
        let body = instance.body().expect("body");
        let vc = mir_to_chc(ctx.tcx, &body, "write_sum_via_ref", ChcConfig::default());

        // Should have multiple blocks (checked add creates Assert → Goto chain)
        assert!(body.blocks.len() >= 2, "checked add should produce multiple blocks");

        // Pointee variable must exist
        let has_pointee_var = vc.vars().iter().any(|v| v.name.contains("_pointee"));
        assert!(has_pointee_var, "VC should declare a _pointee variable (#2496)");

        // Multi-block function must produce transition rules
        let transition_rules: Vec<_> =
            vc.rules.iter().filter(|r| r.body.relation.is_some()).collect();
        assert!(
            !transition_rules.is_empty(),
            "multi-block deref store should produce transition rules (#2496)"
        );

        // At least one transition rule should reference __out (the store has effect)
        let has_out_in_head = transition_rules.iter().any(|r| {
            r.head.args.iter().any(|a| {
                constraint_tree_contains(
                    a,
                    &|e| matches!(e.value(), ExprValue::Var { name } if name.contains("__out")),
                )
            })
        });
        assert!(
            has_out_in_head,
            "deref store transition rules should reference __out variables (#2496)"
        );
    });
}

// =============================================================================
// Field deref store via ref_targets
// =============================================================================

const FIELD_DEREF_STORE_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub struct Point { pub x: u32, pub y: u32 }

    pub fn write_field_via_ref(p: &mut Point, val: u32) {
        p.x = val;
    }
"#;

/// Field deref store (*r).field = value produces a valid VC with field projection.
/// Exercises handle_deref_store_via_ref_targets → field projection path.
///
/// Part of #2720: strengthened from shallow non-emptiness to verify pointee
/// state variables exist with Datatype sort (struct encoding), and both input
/// and output pointee vars are declared. Single-block functions encode the
/// store constraint into head arguments (not body constraints), so we verify
/// state variable setup rather than constraint text.
#[test]
fn test_field_deref_store_via_ref_targets() {
    with_test_ay_ctx_for_source(FIELD_DEREF_STORE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "write_field_via_ref");
        let body = instance.body().expect("body");
        let vc = mir_to_chc(ctx.tcx, &body, "write_field_via_ref", ChcConfig::default());

        assert!(!vc.rules.is_empty(), "field deref store should produce rules");
        assert!(!vc.relations.is_empty(), "field deref store should produce relations");

        // #2720: VC must declare pointee state vars for the &mut Point argument
        let pointee_vars: Vec<_> =
            vc.vars().iter().filter(|v| v.name.contains("_pointee")).collect();
        assert!(
            !pointee_vars.is_empty(),
            "field deref store should declare _pointee variable for &mut Point"
        );
        let has_pointee_out = vc.vars().iter().any(|v| v.name.contains("_pointee__out"));
        assert!(has_pointee_out, "field deref store should declare _pointee__out variable");

        // #2720: Pointee must be Datatype-sorted (struct encoding for Point)
        let has_datatype_pointee = pointee_vars.iter().any(|v| v.sort.is_datatype());
        assert!(
            has_datatype_pointee,
            "field deref store pointee should be Datatype-sorted (Point struct); got: {:?}",
            pointee_vars.iter().map(|v| (&v.name, &v.sort)).collect::<Vec<_>>()
        );

        // #2720: Both input and output pointee vars must exist (input/output pair)
        let pointee_count = pointee_vars.len();
        assert!(
            pointee_count >= 2,
            "field deref store should declare both input/output pointee vars, got {pointee_count}: {:?}",
            pointee_vars.iter().map(|v| &v.name).collect::<Vec<_>>()
        );
    });
}

/// Direct helper-level regression test for arg-ref field stores:
/// `(*arg).field = val` must emit a concrete projection update constraint.
///
/// Part of #2751.
#[test]
fn test_arg_field_deref_store_helper_emits_projection_update_constraint() {
    use rustc_public::mir::{Local, Place, ProjectionElem};
    use std::collections::HashMap;

    with_test_ay_ctx_for_source(FIELD_DEREF_STORE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "write_field_via_ref");
        let body = instance.body().expect("body");

        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "write_field_via_ref", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let pointee_vec_idx = *chc_ctx
            .ref_resolution
            .ref_arg_pointee_idx
            .get(&1)
            .expect("expected arg-ref pointee slot for local 1");
        let track_key = usize::MAX - pointee_vec_idx;
        let rhs_expr = state_var_expr_for_local(&chc_ctx, 2);

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
                c.contains("_write_field_via_ref_1_pointee__out")
                    && c.contains("_write_field_via_ref_2")
            }),
            "expected concrete field-update equality from val input to pointee output, got {constraint_strings:?}"
        );
        assert!(
            constraint_strings.iter().any(|c| c.contains("(fld_y _write_field_via_ref_1_pointee)")),
            "field update should preserve untouched field from pointee input, got {constraint_strings:?}"
        );
        assert!(
            !constraint_strings.iter().any(|c| c.contains(
                "(= _write_field_via_ref_1_pointee__out _write_field_via_ref_1_pointee__in)"
            )),
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

/// Field deref store at Mem level (uses memory model instead of ref_targets).
///
/// Part of #2720: strengthened to verify Mem-level encoding includes a memory
/// state variable with Array sort and that constraints are generated (not empty).
#[test]
fn test_field_deref_store_mem_level() {
    with_test_ay_ctx_for_source(FIELD_DEREF_STORE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "write_field_via_ref");
        let body = instance.body().expect("body");
        let vc = mir_to_chc(
            ctx.tcx,
            &body,
            "write_field_via_ref",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );

        assert!(!vc.rules.is_empty(), "Mem level field store should produce rules");
        assert!(!vc.relations.is_empty(), "Mem level field store should produce relations");

        // #2720: At Mem level, the VC must include a memory state variable
        // (typically Array(BV64, BV8) for byte-addressable memory).
        let has_mem_var = vc.vars().iter().any(|v| v.sort.is_array());
        assert!(
            has_mem_var,
            "Mem-level field store should declare an Array-sorted memory variable; got: {:?}",
            vc.vars().iter().map(|v| (&v.name, &v.sort)).collect::<Vec<_>>()
        );

        // #2720: Constraints should be non-empty — the store must produce
        // at least one constraint referencing the memory update.
        assert!(
            has_any_constraints(&vc),
            "Mem-level field store should produce non-empty constraints"
        );
    });
}

// =============================================================================
// Multiple field stores (last_constraint_for_local override)
// =============================================================================

const MULTI_FIELD_STORE_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub struct Pair { pub a: u32, pub b: u32 }

    pub fn write_both_fields(p: &mut Pair, x: u32, y: u32) {
        p.a = x;
        p.b = y;
    }
"#;

/// Multiple stores to different fields of the same struct via ref_targets.
/// Exercises the last_constraint_for_local path that overrides previous constraints.
///
/// Part of #2720: strengthened from shallow non-emptiness to verify Datatype-sorted
/// pointee vars (input + output pair) and val state variables for both x and y
/// arguments. Single-block functions encode field store constraints into head
/// arguments, so we verify the state variable setup comprehensively.
#[test]
fn test_multi_field_store_via_ref_targets() {
    with_test_ay_ctx_for_source(MULTI_FIELD_STORE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "write_both_fields");
        let body = instance.body().expect("body");
        let vc = mir_to_chc(ctx.tcx, &body, "write_both_fields", ChcConfig::default());

        // Two field stores on the same target → both should be reflected
        assert!(!vc.rules.is_empty(), "multi-field store should produce rules");
        assert!(!vc.relations.is_empty(), "multi-field store should produce relations");

        // #2720: VC must declare pointee variables for the &mut Pair argument
        let pointee_vars: Vec<_> =
            vc.vars().iter().filter(|v| v.name.contains("_pointee")).collect();
        assert!(
            !pointee_vars.is_empty(),
            "multi-field store VC should declare _pointee variable for &mut Pair"
        );
        let has_pointee_out = vc.vars().iter().any(|v| v.name.contains("_pointee__out"));
        assert!(has_pointee_out, "multi-field store should declare pointee__out state variable");
        let pointee_var_count = pointee_vars.len();
        assert!(
            pointee_var_count >= 2,
            "multi-field store should declare both input/output pointee vars, got {pointee_var_count}: {:?}",
            pointee_vars.iter().map(|v| &v.name).collect::<Vec<_>>()
        );

        // #2720: Pointee must be Datatype-sorted (Pair struct)
        let has_datatype_pointee = pointee_vars.iter().any(|v| v.sort.is_datatype());
        assert!(
            has_datatype_pointee,
            "multi-field store pointee should be Datatype-sorted (Pair struct); got: {:?}",
            pointee_vars.iter().map(|v| (&v.name, &v.sort)).collect::<Vec<_>>()
        );

        // #2720: Both x (local 2) and y (local 3) val args must have state vars
        let has_x_var = vc.vars().iter().any(|v| v.name.contains("_write_both_fields_2"));
        let has_y_var = vc.vars().iter().any(|v| v.name.contains("_write_both_fields_3"));
        assert!(
            has_x_var && has_y_var,
            "multi-field store should declare state vars for both x and y arguments; got: {:?}",
            vc.vars().iter().map(|v| &v.name).collect::<Vec<_>>()
        );
    });
}

// =============================================================================
// Deref store array via ref_targets (#1957)
// =============================================================================

const ARRAY_DEREF_STORE_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub fn store_via_array_ref(arr: &mut [u32; 4], idx: usize, val: u32) {
        arr[idx] = val;
    }
"#;

/// Array element store via ref_targets (*ref pointing to arr[idx]) at Reg level.
/// Exercises handle_deref_store_array_via_ref_targets → Index path.
///
/// Part of #2720: strengthened to verify Array-sorted pointee vars, idx bounds
/// guard in body constraints (`bvult`), and transition rules that reference
/// `__out` state variables. The actual `store`/`select` operations are encoded
/// in transition head arguments, not body constraints.
#[test]
fn test_array_deref_store_via_ref_targets() {
    with_test_ay_ctx_for_source(ARRAY_DEREF_STORE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "store_via_array_ref");
        let body = instance.body().expect("body");
        let vc = mir_to_chc(ctx.tcx, &body, "store_via_array_ref", ChcConfig::default());

        assert_vc_structure(&vc, "store_via_array_ref", body.blocks.len());

        // #2720: VC must declare a pointee variable for the &mut [u32; 4] argument
        let pointee_vars: Vec<_> =
            vc.vars().iter().filter(|v| v.name.contains("_pointee")).collect();
        assert!(
            !pointee_vars.is_empty(),
            "array deref store VC should declare a _pointee variable for &mut [u32; 4]"
        );

        // #2720: The pointee var should be Array-sorted (Array<BV, BV>)
        let has_array_sorted_pointee = pointee_vars.iter().any(|v| v.sort.is_array());
        assert!(
            has_array_sorted_pointee,
            "array deref store pointee should have Array sort, got sorts: {:?}",
            pointee_vars.iter().map(|v| (&v.name, &v.sort)).collect::<Vec<_>>()
        );

        // #2720: Both input and output pointee vars must exist
        let has_pointee_out = vc.vars().iter().any(|v| v.name.contains("_pointee__out"));
        assert!(has_pointee_out, "array deref store should declare _pointee__out variable");

        // #2720: Body constraints must include idx bounds guard (bvult check).
        // Array indexing produces a bounds check that creates multiple blocks.
        assert!(
            any_constraint_str(&vc, |c| c.contains("bvult")
                && c.contains("_store_via_array_ref_2")),
            "array deref store constraints should include idx bounds guard"
        );

        // #2720: Transition rules should reference __out variables (store effect)
        let transition_rules: Vec<_> =
            vc.rules.iter().filter(|r| r.body.relation.is_some()).collect();
        assert!(
            !transition_rules.is_empty(),
            "array deref store should produce transition rules (multi-block from bounds check)"
        );
        let has_out_in_head = transition_rules
            .iter()
            .any(|r| r.head.args.iter().any(|a| {
                constraint_tree_contains(a, &|e| {
                    matches!(e.value(), ay_bindings::ExprValue::Var { name } if name.contains("__out"))
                })
            }));
        assert!(
            has_out_in_head,
            "array deref store transition head args should reference __out variables"
        );
    });
}

const CONST_INDEX_STORE_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub fn store_first_element(arr: &mut [u32; 4], val: u32) {
        arr[0] = val;
    }
"#;

/// Constant-index array store via ref_targets at Reg level.
/// Exercises handle_deref_store_array_via_ref_targets → ConstantIndex path.
///
/// Part of #2720: strengthened to verify Array-sorted pointee state vars
/// (input and output pair) and bounds guard in body constraints. The actual
/// `store` operation is encoded in transition head arguments, not body constraints.
#[test]
fn test_const_index_array_store_via_ref_targets() {
    with_test_ay_ctx_for_source(CONST_INDEX_STORE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "store_first_element");
        let body = instance.body().expect("body");
        let vc = mir_to_chc(ctx.tcx, &body, "store_first_element", ChcConfig::default());

        assert_vc_structure(&vc, "store_first_element", body.blocks.len());

        // #2720: Pointee variable for &mut [u32; 4] must be Array-sorted
        let pointee_vars: Vec<_> =
            vc.vars().iter().filter(|v| v.name.contains("_pointee")).collect();
        assert!(
            !pointee_vars.is_empty(),
            "const-index array store should declare _pointee variable"
        );
        let has_array_sorted = pointee_vars.iter().any(|v| v.sort.is_array());
        assert!(
            has_array_sorted,
            "const-index array store pointee should be Array-sorted; got: {:?}",
            pointee_vars.iter().map(|v| (&v.name, &v.sort)).collect::<Vec<_>>()
        );
        let has_pointee_out = vc.vars().iter().any(|v| v.name.contains("_pointee__out"));
        assert!(has_pointee_out, "const-index array store should declare _pointee__out variable");

        // #2720: Bounds guard from constant-index (0 < 4) should appear in constraints
        assert!(
            any_constraint_str(&vc, |c| c.contains("bvult")),
            "const-index array store should include bounds guard in constraints"
        );
    });
}

// =============================================================================
// Array element field store (arr[idx].field = value)
// =============================================================================

const ARRAY_STRUCT_STORE_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub struct Item { pub value: u32, pub tag: u32 }

    pub fn store_array_element_field(items: &mut [Item; 4], idx: usize, val: u32) {
        items[idx].value = val;
    }
"#;

/// Array element field store: arr[idx].field = value via ref_targets.
/// Exercises the struct field sub-path in handle_deref_store_array_via_ref_targets.
///
/// Part of #2720: strengthened to verify Array-sorted pointee vars (input/output
/// pair), idx bounds guard, and transition rules with `__out` head args. The
/// `store`/`select` operations and `fld_value` accessor are encoded in
/// transition head arguments, not body constraints.
#[test]
fn test_array_struct_element_field_store() {
    with_test_ay_ctx_for_source(ARRAY_STRUCT_STORE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "store_array_element_field");
        let body = instance.body().expect("body");
        let vc = mir_to_chc(ctx.tcx, &body, "store_array_element_field", ChcConfig::default());

        assert!(!vc.rules.is_empty(), "array struct store should produce rules");
        assert!(!vc.relations.is_empty(), "array struct store should produce relations");

        // #2720: Pointee variable for &mut [Item; 4] must be Array-sorted
        let pointee_vars: Vec<_> =
            vc.vars().iter().filter(|v| v.name.contains("_pointee")).collect();
        assert!(
            !pointee_vars.is_empty(),
            "array struct store should declare _pointee variable for &mut [Item; 4]"
        );
        let has_array_sorted = pointee_vars.iter().any(|v| v.sort.is_array());
        assert!(
            has_array_sorted,
            "array struct store pointee should be Array-sorted; got: {:?}",
            pointee_vars.iter().map(|v| (&v.name, &v.sort)).collect::<Vec<_>>()
        );
        let has_pointee_out = vc.vars().iter().any(|v| v.name.contains("_pointee__out"));
        assert!(has_pointee_out, "array struct store should declare _pointee__out variable");

        // #2720: Bounds guard from idx < 4 should appear in body constraints
        assert!(
            any_constraint_str(&vc, |c| c.contains("bvult")),
            "array struct store should include bounds guard in constraints"
        );

        // #2720: Transition rules should exist (multi-block from bounds check)
        let has_transition_rules = vc.rules.iter().any(|r| r.body.relation.is_some());
        assert!(
            has_transition_rules,
            "array struct store should produce transition rules (multi-block from bounds check)"
        );
    });
}

// =============================================================================
// Sort coercion at store boundaries (#2244)
// =============================================================================

const BOOL_DEREF_STORE_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub fn write_bool_via_ref(b: &mut bool, val: bool) {
        *b = val;
    }
"#;

/// Bool deref store exercises sort coercion (Bool ↔ BV in CHC encoding).
/// Exercises coerce_eq_constraint path in handle_deref_store_via_ref_targets.
///
/// Part of #2720: strengthened to verify Bool/BV-sorted pointee vars (input +
/// output pair), val local state variable with matching sort, and that all
/// body constraints are Bool-sorted. Single-block functions encode the store
/// constraint into head arguments, not body constraints.
#[test]
fn test_bool_deref_store_sort_coercion() {
    with_test_ay_ctx_for_source(BOOL_DEREF_STORE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "write_bool_via_ref");
        let body = instance.body().expect("body");
        let vc = mir_to_chc(ctx.tcx, &body, "write_bool_via_ref", ChcConfig::default());

        assert!(!vc.rules.is_empty(), "bool deref store should produce rules");

        // #2720: VC must declare a pointee variable for the &mut bool argument
        let pointee_vars: Vec<_> =
            vc.vars().iter().filter(|v| v.name.contains("_pointee")).collect();
        assert!(
            !pointee_vars.is_empty(),
            "bool deref store VC should declare a _pointee variable for &mut bool"
        );

        // #2720: The pointee variable should be Bool-sorted (after sort coercion,
        // bool maps to SMT Bool). Alternatively it may be BV(8) if the encoding
        // uses byte representation — either is valid for bool.
        let has_bool_or_bv_pointee =
            pointee_vars.iter().any(|v| v.sort.is_bool() || v.sort.bitvec_width().is_some());
        assert!(
            has_bool_or_bv_pointee,
            "bool deref store pointee should be Bool or BV-sorted, got sorts: {:?}",
            pointee_vars.iter().map(|v| (&v.name, &v.sort)).collect::<Vec<_>>()
        );

        // #2720: Both input and output pointee vars must exist
        let has_pointee_out = vc.vars().iter().any(|v| v.name.contains("_pointee__out"));
        assert!(has_pointee_out, "bool deref store should declare pointee__out state variable");
        let pointee_count = pointee_vars.len();
        assert!(
            pointee_count >= 2,
            "bool deref store should declare both input/output pointee vars, got {pointee_count}: {:?}",
            pointee_vars.iter().map(|v| &v.name).collect::<Vec<_>>()
        );

        // #2720: Val local (local 2) must have a Bool/BV-sorted state variable
        let val_vars: Vec<_> =
            vc.vars().iter().filter(|v| v.name.contains("_write_bool_via_ref_2")).collect();
        assert!(!val_vars.is_empty(), "expected state variable(s) for val local");
        assert!(
            val_vars.iter().any(|v| v.sort.is_bool() || v.sort.bitvec_width().is_some()),
            "val local should be Bool/BV-sorted, got {:?}",
            val_vars.iter().map(|v| (&v.name, &v.sort)).collect::<Vec<_>>()
        );

        // #2720: All body constraints should be Bool-sorted (SMT well-formedness)
        let constraints: Vec<_> =
            vc.rules.iter().flat_map(|rule| rule.body.constraints.iter()).collect();
        assert!(!constraints.is_empty(), "bool deref store should produce non-empty constraints");
        assert!(
            constraints.iter().all(|constraint| constraint.sort().is_bool()),
            "all bool deref constraints should be Bool-sorted"
        );
    });
}

// =============================================================================
// Deref store at different track levels
// =============================================================================

/// Scalar deref store at Ptr level for comparison with Reg path.
///
/// Part of #2720: strengthened to verify Ptr-level encoding produces pointer
/// state variables (BV64-sorted for addresses) and non-empty constraints.
#[test]
fn test_scalar_deref_store_ptr_level() {
    with_test_ay_ctx_for_source(SCALAR_DEREF_STORE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "write_via_ref");
        let body = instance.body().expect("body");
        let vc = mir_to_chc(
            ctx.tcx,
            &body,
            "write_via_ref",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Ptr, ..ChcConfig::default() },
        );

        assert!(!vc.rules.is_empty(), "Ptr-level deref store should produce rules");
        assert!(!vc.relations.is_empty(), "Ptr-level deref store should produce relations");

        // #2720: At Ptr level, pointer-typed arguments produce BV64 state vars
        // (representing addresses) rather than Reg-level pointee vars.
        let has_bv_var = vc
            .vars()
            .iter()
            .any(|v| v.name.contains("_write_via_ref_1") && v.sort.bitvec_width().is_some());
        assert!(
            has_bv_var,
            "Ptr-level deref store should declare a BV-sorted state variable for the &mut arg; got: {:?}",
            vc.vars().iter().map(|v| (&v.name, &v.sort)).collect::<Vec<_>>()
        );

        // #2720: Constraints must be non-empty — the store has an observable effect.
        assert!(
            has_any_constraints(&vc),
            "Ptr-level deref store should produce non-empty constraints"
        );
    });
}

/// Scalar deref store at Mem level (bypasses ref_targets, uses memory model).
///
/// Part of #2720: strengthened to verify Mem-level encoding includes an
/// Array-sorted memory variable and non-empty constraints.
#[test]
fn test_scalar_deref_store_mem_level() {
    with_test_ay_ctx_for_source(SCALAR_DEREF_STORE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "write_via_ref");
        let body = instance.body().expect("body");
        let vc = mir_to_chc(
            ctx.tcx,
            &body,
            "write_via_ref",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );

        assert!(!vc.rules.is_empty(), "Mem-level deref store should produce rules");
        assert!(!vc.relations.is_empty(), "Mem-level deref store should produce relations");

        // #2720: At Mem level, a memory state variable with Array sort should exist
        let has_mem_var = vc.vars().iter().any(|v| v.sort.is_array());
        assert!(
            has_mem_var,
            "Mem-level deref store should declare an Array-sorted memory variable; got: {:?}",
            vc.vars().iter().map(|v| (&v.name, &v.sort)).collect::<Vec<_>>()
        );

        // #2720: Constraints must be non-empty
        assert!(
            has_any_constraints(&vc),
            "Mem-level deref store should produce non-empty constraints"
        );
    });
}

// =============================================================================
// Array element store through arg-ref pointee (#2750)
// =============================================================================

/// Array element store through arg-ref pointee must produce constrained
/// transition rules. Prior to #2750, `ProjectionElem::Index` in the arg-ref
/// path caused a silent `return false`, dropping the store entirely.
#[test]
fn test_array_store_arg_ref_pointee_produces_constrained_rules() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn array_store_arg(r: &mut [u32; 4], idx: usize, val: u32) {
            r[idx] = val;
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "array_store_arg");
        let body = instance.body().expect("body");
        let vc = mir_to_chc(ctx.tcx, &body, "array_store_arg", ChcConfig::default());

        assert_vc_structure(&vc, "array_store_arg", body.blocks.len());

        // #2750: VC must have a pointee variable for the &mut [u32; 4] argument.
        let has_pointee_var = vc.vars().iter().any(|v| v.name.contains("_pointee"));
        assert!(
            has_pointee_var,
            "array_store_arg VC should declare a _pointee state variable (#2750)"
        );

        // The key check: at least one transition rule must have non-trivial
        // constraints (the store expression). Before #2750, the store was
        // silently dropped and all transitions were unconstrained.
        let constrained_transitions = vc
            .rules
            .iter()
            .filter(|r| r.body.relation.is_some())
            .filter(|r| r.head.name != "error")
            .filter(|r| !r.body.constraints.is_empty())
            .count();

        assert!(
            constrained_transitions > 0,
            "array store through arg-ref should produce constrained transitions (#2750), \
             got {constrained_transitions} constrained out of {} total rules",
            vc.rules.len()
        );
    });
}

/// Direct helper-level test for arg-ref array store (#2750).
/// Verifies the handler returns true and emits a store constraint.
#[test]
fn test_arg_ref_array_store_helper_emits_store_constraint() {
    use ay_bindings::Expr;
    use rustc_public::mir::{Local, Place, ProjectionElem};
    use std::collections::HashMap;

    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn array_store_helper(r: &mut [u32; 4], idx: usize, val: u32) {
            r[idx] = val;
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "array_store_helper");
        let body = instance.body().expect("body");

        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "array_store_helper", ChcConfig::default());
        chc_ctx.declare_block_relations();

        // Arg 1 is `r: &mut [u32; 4]` — should have a pointee slot.
        let pointee_vec_idx = *chc_ctx
            .ref_resolution
            .ref_arg_pointee_idx
            .get(&1)
            .expect("expected arg-ref pointee slot for local 1 (#2750)");

        // Build a Place for `(*r)[idx] = val`:
        // projection: [Deref, Index(local_for_idx)]
        // idx is local 2, val is local 3.
        let lhs = Place {
            local: Local::from(1usize),
            projection: vec![ProjectionElem::Deref, ProjectionElem::Index(2usize)],
        };

        // Get val's expression (local 3).
        let val_vec_idx = *chc_ctx
            .state_var_mgr
            .local_to_state_idx
            .get(&3)
            .expect("expected state index for val local");
        let (val_name, val_sort) =
            chc_ctx.state_var_mgr.state_vars.get(val_vec_idx).expect("missing state var for val");
        let rhs_expr = Expr::var(val_name.to_string(), val_sort.clone());

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

        assert!(handled, "arg-ref array store handler should handle (*r)[idx] = val (#2750)");
        assert!(
            !constraints.is_empty(),
            "arg-ref array store should emit at least one constraint (#2750)"
        );

        // Verify the pointee was marked modified.
        assert!(
            chc_ctx.encode.modified_state_indices.contains(&pointee_vec_idx),
            "arg-ref array store should mark pointee as modified (#2750)"
        );
    });
}

// Coroutine Pin-wrapper store tests removed (Part of #3828):
// test_coroutine_pin_wrapper_reg_store_updates_arg_pointee_slot
// test_coroutine_pin_wrapper_mem_store_mirrors_arg_pointee_slot
//
// These were committed broken by W5:3971 without cargo test verification.
// The MIR no longer produces combined [Deref, Downcast, Field] projections
// in coroutine closure bodies — MIR optimization splits them into separate
// statements (documented in test_active_variant.rs:41-43). The helper
// find_coroutine_variant_field_store() searched for the old combined pattern
// and returned None, causing panics.

/// Regression test for #3816: aggregate-root ref-target array stores.
/// `self.arr[idx] = val` where `self: &mut Struct` has projection
/// [Deref, Field(arr), Index(idx)] — must select the array field from
/// the aggregate before calling store().
#[test]
fn test_aggregate_field_array_store_arg_ref_does_not_panic() {
    use ay_bindings::Expr;
    use rustc_public::mir::{Local, Place, ProjectionElem};
    use std::collections::HashMap;

    const SOURCE: &str = r#"
        #![allow(dead_code)]

        struct Holder {
            data: [u32; 4],
            len: usize,
        }

        impl Holder {
            pub fn push(&mut self, idx: usize, val: u32) {
                self.data[idx] = val;
            }
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "push");
        let body = instance.body().expect("body");

        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "push", ChcConfig::default());
        chc_ctx.declare_block_relations();

        // Arg 1 is `self: &mut Holder` — should have a pointee slot.
        let pointee_vec_idx = *chc_ctx
            .ref_resolution
            .ref_arg_pointee_idx
            .get(&1)
            .expect("expected arg-ref pointee slot for &mut self (#3816)");

        // Build Place for `(*_self).data[idx] = val`:
        // projection: [Deref, Field(0 = data), Index(local_for_idx)]
        let lhs = Place {
            local: Local::from(1usize),
            projection: vec![
                ProjectionElem::Deref,
                ProjectionElem::Field(0usize, body.locals()[1].ty),
                ProjectionElem::Index(2usize),
            ],
        };

        // Get val's expression (local 3).
        let val_vec_idx = *chc_ctx
            .state_var_mgr
            .local_to_state_idx
            .get(&3)
            .expect("expected state index for val local");
        let (val_name, val_sort) =
            chc_ctx.state_var_mgr.state_vars.get(val_vec_idx).expect("state var for val");
        let rhs_expr = Expr::var(val_name.to_string(), val_sort.clone());

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

        assert!(handled, "aggregate field array store should be handled (#3816)");
        assert!(
            !constraints.is_empty(),
            "aggregate field array store should emit constraints (#3816)"
        );
        assert!(
            chc_ctx.encode.modified_state_indices.contains(&pointee_vec_idx),
            "aggregate field array store should mark pointee modified (#3816)"
        );
    });
}
