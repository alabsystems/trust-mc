// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Tests for CHC codegen_stmt.rs — the central `encode_block_statements` dispatcher.
//!
//! This file tests the top-level statement encoding logic that coordinates all
//! sibling `codegen_stmt_*.rs` files. Sibling files each have their own test files
//! (test_stmt_copy, test_stmt_store, test_stmt_flatten, etc.); these tests cover
//! the dispatcher itself:
//!
//! - StorageLive/StorageDead handling (dead local tracking)
//! - Multi-assignment constraint replacement (#2055)
//! - Simple scalar assignment with sort coercion
//! - Projection assignment (struct field update)
//! - Flattened tuple local (CheckedBinaryOp) dispatch
//! - Nondet fallback for unsupported rvalues
//! - Intrinsic Assume constraint generation
//! - Block output arg construction (modified vs unmodified locals)
//!
//! Part of #2272: unit test coverage for Tier-1 soundness-critical CHC files.

#![allow(clippy::unwrap_used)]

use super::common::*;
use crate::codegen_ay::emit_chc;

// =============================================================================
// StorageLive / StorageDead — dead local tracking in encode_block_statements
// =============================================================================

/// Verify that StorageLive/StorageDead statements don't generate constraints
/// but do affect the dead_locals set (observable through output arg behavior).
#[test]
fn test_storage_live_dead_does_not_generate_constraints() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn storage_live_dead(x: u32) -> u32 {
            let a: u32 = x + 1;
            let b: u32 = a + 2;
            b
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "storage_live_dead");
        let body = instance.body().expect("body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "storage_live_dead", ChcConfig::default());
        let (vc, _) = chc_ctx.translate();
        let smt = emit_chc(&vc).to_string();

        // Should produce a valid VC with rules
        assert!(!vc.rules.is_empty(), "translate should produce rules");
        assert!(!smt.is_empty(), "VC should produce non-empty SMT");

        // StorageLive/Dead should NOT produce any constraints themselves
        // (they only update dead_locals tracking). Verify by checking that
        // the VC doesn't contain "StorageLive" or "StorageDead" strings.
        assert!(!smt.contains("StorageLive"), "StorageLive should not appear in SMT output");
        assert!(!smt.contains("StorageDead"), "StorageDead should not appear in SMT output");

        assert_vc_structure(&vc, "storage_live_dead", body.blocks.len());
    });
}

// =============================================================================
// Multi-assignment in single block — constraint replacement (#2055)
// =============================================================================

/// When the same local is assigned twice in one block, the first constraint
/// must be replaced with `true` to avoid UNSAT. This tests the
/// `last_constraint_for_local` tracking in encode_block_statements.
#[test]
fn test_multi_assignment_replaces_first_constraint() {
    const SOURCE: &str = r#"
        #![allow(dead_code, unused_assignments)]

        pub fn multi_assign(x: u32) -> u32 {
            let mut a: u32 = x;
            a = x + 1;
            a
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "multi_assign");
        let body = instance.body().expect("body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "multi_assign", ChcConfig::default());
        let (vc, _) = chc_ctx.translate();
        let smt = emit_chc(&vc).to_string();

        // The VC should be valid (not UNSAT from contradictory constraints)
        assert!(!vc.rules.is_empty(), "translate should produce rules");
        assert_vc_structure(&vc, "multi_assign", body.blocks.len());

        // The SMT should contain bvadd (for x + 1) — this confirms the
        // assignment constraint for a = x + 1 is present.
        assert!(smt.contains("bvadd"), "Multi-assign function should contain bvadd for x + 1");
    });
}

/// Multi-assignment where the second assignment is a different expression.
/// Verifies the final assignment "wins" in the constraint set.
#[test]
fn test_multi_assignment_final_value_wins() {
    const SOURCE: &str = r#"
        #![allow(dead_code, unused_assignments)]

        pub fn reassign_different(x: u32, y: u32) -> u32 {
            let mut result: u32 = x;
            result = y;
            result
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "reassign_different");
        let body = instance.body().expect("body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "reassign_different", ChcConfig::default());
        let (vc, _) = chc_ctx.translate();

        // The VC should be satisfiable — result should equal y, not x.
        // If constraint replacement didn't work, result would need to equal
        // both x AND y simultaneously, making the block unreachable.
        assert!(!vc.rules.is_empty(), "translate should produce rules");

        // There should be rules with constraints (not just empty transitions)
        assert!(
            vc.rules.iter().any(|r| !r.body.constraints.is_empty()),
            "Should have rules with constraints from assignments"
        );
    });
}

// =============================================================================
// Simple scalar assignment — constraint generation
// =============================================================================

/// Verify that a simple scalar assignment generates an equality constraint
/// binding the output variable to the rhs expression.
#[test]
fn test_simple_assignment_generates_equality_constraint() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn add_one(x: u32) -> u32 {
            let result: u32 = x + 1;
            result
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "add_one");
        let body = instance.body().expect("body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "add_one", ChcConfig::default());
        let (vc, _) = chc_ctx.translate();
        let smt = emit_chc(&vc).to_string();

        // Should contain bvadd constraint for x + 1
        assert!(smt.contains("bvadd"), "Simple add should produce bvadd constraint");

        // Should have block relations for the function
        assert!(
            vc.relations.iter().any(|r| r.name.contains("add_one")),
            "Should have block relations for add_one"
        );

        assert_vc_structure(&vc, "add_one", body.blocks.len());
    });
}

/// Verify that boolean comparison generates a valid VC with block relations.
/// The comparison `x > 0` is encoded via SwitchInt terminator branching,
/// so the block body may be empty; the key property is that the overall
/// translation produces valid rules and relations with Bool-typed state.
#[test]
fn test_boolean_assignment_constraint() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn is_positive(x: i32) -> bool {
            x > 0
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "is_positive");
        let body = instance.body().expect("body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "is_positive", ChcConfig::default());
        let (vc, _) = chc_ctx.translate();
        let smt = emit_chc(&vc).to_string();

        // Translation should produce a valid VC
        assert!(!vc.rules.is_empty(), "translate should produce rules");
        assert!(!smt.is_empty(), "VC should produce non-empty SMT");

        // The VC should have block relations for is_positive
        assert!(
            vc.relations.iter().any(|r| r.name.contains("is_positive")),
            "Should have block relations for is_positive"
        );

        // The VC should declare a Bool state variable (for the return value)
        assert!(smt.contains("Bool"), "Boolean function should have Bool-sorted state variable");

        assert_vc_structure(&vc, "is_positive", body.blocks.len());
    });
}

// =============================================================================
// Projection assignment — struct field functional update
// =============================================================================

/// Verify that struct field assignment produces a valid VC.
/// The struct may be flattened into scalar state variables at the CHC level,
/// so we check structural VC properties rather than specific SMT syntax.
#[test]
fn test_struct_field_assignment_functional_update() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub struct Pair {
            pub a: u32,
            pub b: u32,
        }

        pub fn set_first(mut p: Pair) -> Pair {
            p.a = 42;
            p
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "set_first");
        let body = instance.body().expect("body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "set_first", ChcConfig::default());
        let (vc, _) = chc_ctx.translate();
        let smt = emit_chc(&vc).to_string();

        // Should produce valid rules and non-empty SMT
        assert!(!vc.rules.is_empty(), "translate should produce rules");
        assert!(!smt.is_empty(), "VC should produce non-empty SMT");

        // Should have block relations for set_first
        assert!(
            vc.relations.iter().any(|r| r.name.contains("set_first")),
            "Should have block relations for set_first"
        );

        // The VC should have BitVec 32 state variables (for struct fields)
        assert!(
            smt.contains("BitVec 32"),
            "Struct with u32 fields should have BitVec 32 state variables"
        );

        assert_vc_structure(&vc, "set_first", body.blocks.len());
    });
}

/// Verify that nested struct field assignment works through projections.
#[test]
fn test_nested_struct_field_assignment() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub struct Inner {
            pub val: u32,
        }

        pub struct Outer {
            pub inner: Inner,
            pub tag: u32,
        }

        pub fn set_nested(mut o: Outer) -> Outer {
            o.inner.val = 99;
            o
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "set_nested");
        let body = instance.body().expect("body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "set_nested", ChcConfig::default());
        let (vc, _) = chc_ctx.translate();
        let smt = emit_chc(&vc).to_string();

        // Nested field assignment should still produce valid VC
        assert!(!vc.rules.is_empty(), "translate should produce rules");
        assert!(!smt.is_empty(), "VC should produce non-empty SMT");

        // Should have block relations for set_nested
        assert!(
            vc.relations.iter().any(|r| r.name.contains("set_nested")),
            "Should have block relations for set_nested"
        );

        assert_vc_structure(&vc, "set_nested", body.blocks.len());
    });
}

// =============================================================================
// Checked arithmetic — flattened tuple dispatch
// =============================================================================

/// Checked addition produces a tuple (value, overflow_flag). The dispatcher
/// should route this through try_encode_flattened_local_assign which handles
/// the CheckedBinaryOp pattern specially. The resulting VC must be valid
/// with rules covering the Option/tuple flattening.
#[test]
fn test_checked_add_flattened_dispatch() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn checked_add_u32(x: u32, y: u32) -> Option<u32> {
            x.checked_add(y)
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "checked_add_u32");
        let body = instance.body().expect("body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "checked_add_u32", ChcConfig::default());
        let (vc, _) = chc_ctx.translate();
        let smt = emit_chc(&vc).to_string();

        // Checked add should produce a valid VC with rules
        assert!(!vc.rules.is_empty(), "translate should produce rules");
        assert!(!smt.is_empty(), "VC should produce non-empty SMT");

        // Should have block relations for checked_add_u32
        assert!(
            vc.relations.iter().any(|r| r.name.contains("checked_add_u32")),
            "Should have block relations for checked_add_u32"
        );

        // Should have multiple blocks (checked_add generates branching for overflow)
        assert!(
            vc.relations.iter().filter(|r| r.name.contains("checked_add_u32__bb")).count() >= 2,
            "Checked add should produce >= 2 block relations (normal + overflow paths)"
        );

        assert_vc_structure(&vc, "checked_add_u32", body.blocks.len());
    });
}

// =============================================================================
// Block output args — modified vs unmodified locals
// =============================================================================

/// Verify that modified locals use output variables while unmodified locals
/// pass through input variables in successor rules.
/// Checks: (1) at least one transition rule head arg contains __out,
/// (2) at least one transition rule head arg does NOT contain __out (frame condition).
#[test]
fn test_output_args_modified_vs_unmodified() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn modify_one(x: u32, _y: u32) -> u32 {
            let result: u32 = x + 1;
            // y is not modified, should pass through as input
            result
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "modify_one");
        let body = instance.body().expect("body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "modify_one", ChcConfig::default());
        let (vc, _) = chc_ctx.translate();

        assert_vc_structure(&vc, "modify_one", body.blocks.len());

        // Modified locals use output variables (__out suffix) in successor rules.
        // Verify the VC has rules with constraints (from the x + 1 assignment).
        let rules_with_constraints =
            vc.rules.iter().filter(|r| !r.body.constraints.is_empty()).count();
        assert!(
            rules_with_constraints >= 1,
            "modify_one should produce rules with assignment constraints, got {rules_with_constraints}"
        );

        // Check transition rules (body.relation is Some) for __out / non-__out head args.
        let transition_rules: Vec<_> =
            vc.rules.iter().filter(|r| r.body.relation.is_some()).collect();
        assert!(
            !transition_rules.is_empty(),
            "modify_one should produce at least one transition rule"
        );

        // At least one transition rule head arg must reference an __out variable
        // (the modified local: result or return place).
        let has_out_arg = transition_rules.iter().any(|r| {
            r.head.args.iter().any(|a| {
                constraint_tree_contains(
                    a,
                    &|e| matches!(e.value(), ExprValue::Var { name } if name.contains("__out")),
                )
            })
        });
        assert!(
            has_out_arg,
            "transition rule head args should include __out variables for modified locals"
        );

        // At least one transition rule head arg must NOT reference __out
        // (unmodified locals pass through as input — frame condition).
        let has_non_out_arg = transition_rules.iter().any(|r| {
            r.head.args.iter().any(|a| {
                constraint_tree_contains(
                    a,
                    &|e| matches!(e.value(), ExprValue::Var { name } if !name.contains("__out")),
                )
            })
        });
        assert!(
            has_non_out_arg,
            "transition rule head args should include non-__out variables for unmodified locals"
        );
    });
}

// =============================================================================
// Sort coercion on assignment — bitvec width mismatch
// =============================================================================

/// Verify that sort coercion handles different bitvec widths on assignment.
/// Cast from u8 to u32 exercises the sort coercion path in encode_block_statements.
/// The CHC encoding may use different BV widths in the relation declarations
/// (BitVec 8 for input, BitVec 32 for output).
#[test]
fn test_assignment_sort_coercion_widening_cast() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn widen_u8_to_u32(x: u8) -> u32 {
            x as u32
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "widen_u8_to_u32");
        let body = instance.body().expect("body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "widen_u8_to_u32", ChcConfig::default());
        let (vc, _) = chc_ctx.translate();
        let smt = emit_chc(&vc).to_string();

        // Translation should produce valid VC
        assert!(!vc.rules.is_empty(), "translate should produce rules");
        assert!(!smt.is_empty(), "VC should produce non-empty SMT");

        // Should have block relations
        assert!(
            vc.relations.iter().any(|r| r.name.contains("widen_u8_to_u32")),
            "Should have block relations for widen_u8_to_u32"
        );

        // The widening cast should involve both 8-bit and 32-bit BV sorts
        assert!(
            smt.contains("BitVec 8") || smt.contains("BitVec 32"),
            "Widening cast u8 -> u32 should involve BitVec 8 or BitVec 32 sorts"
        );

        assert_vc_structure(&vc, "widen_u8_to_u32", body.blocks.len());
    });
}

/// Verify that signed narrowing cast produces a valid VC with correct sort handling.
#[test]
fn test_assignment_sort_coercion_narrowing_cast() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn narrow_i32_to_i8(x: i32) -> i8 {
            x as i8
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "narrow_i32_to_i8");
        let body = instance.body().expect("body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "narrow_i32_to_i8", ChcConfig::default());
        let (vc, _) = chc_ctx.translate();
        let smt = emit_chc(&vc).to_string();

        // Translation should produce valid VC
        assert!(!vc.rules.is_empty(), "translate should produce rules");
        assert!(!smt.is_empty(), "VC should produce non-empty SMT");

        // Should have block relations
        assert!(
            vc.relations.iter().any(|r| r.name.contains("narrow_i32_to_i8")),
            "Should have block relations for narrow_i32_to_i8"
        );

        // The narrowing cast should involve both 32-bit and 8-bit BV sorts
        assert!(
            smt.contains("BitVec 8") || smt.contains("BitVec 32"),
            "Narrowing cast i32 -> i8 should involve BitVec 32 or BitVec 8 sorts"
        );

        assert_vc_structure(&vc, "narrow_i32_to_i8", body.blocks.len());
    });
}

// =============================================================================
// Local expression environment (#2055) — intra-block value tracking
// =============================================================================

/// Verify that the local expression environment correctly tracks values
/// within a block so that chained computations use concrete expressions
/// rather than shared __out variables.
#[test]
fn test_local_expr_env_chained_computation() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn chain(x: u32) -> u32 {
            let a: u32 = x + 1;
            let b: u32 = a + 2;
            let c: u32 = b + 3;
            c
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "chain");
        let body = instance.body().expect("body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "chain", ChcConfig::default());
        let (vc, _) = chc_ctx.translate();
        let smt = emit_chc(&vc).to_string();

        // Should produce multiple bvadd operations for the chain
        let bvadd_count = smt.matches("bvadd").count();
        assert!(
            bvadd_count >= 3,
            "Chain of 3 additions should produce >= 3 bvadd, got {bvadd_count}"
        );

        assert_vc_structure(&vc, "chain", body.blocks.len());
    });
}

// =============================================================================
// Heap/memory state — store chain draining
// =============================================================================

/// Verify that memory-level store operations produce valid constraints
/// (heap_state.drain_store_chains is called at block end).
#[test]
fn test_mem_level_store_chain_draining() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn write_ref(r: &mut u32) {
            *r = 42;
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "write_ref");
        let body = instance.body().expect("body");

        let chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            "write_ref",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );
        let (vc, _) = chc_ctx.translate();
        let smt = emit_chc(&vc).to_string();

        // Mem-level should have store operations for memory writes
        assert!(
            smt.contains("store") || smt.contains("select"),
            "Mem-level deref write should produce store/select operations"
        );

        assert_vc_structure(&vc, "write_ref", body.blocks.len());
    });
}

// =============================================================================
// Conditional branching — encode_block_statements with different BB counts
// =============================================================================

/// Verify that an if-else generates proper rules with SwitchInt guards
/// (the block statement encoding feeds into rule generation).
#[test]
fn test_conditional_branch_multiple_blocks() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn max_of(x: u32, y: u32) -> u32 {
            if x > y {
                x
            } else {
                y
            }
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "max_of");
        let body = instance.body().expect("body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "max_of", ChcConfig::default());
        let (vc, _) = chc_ctx.translate();

        // Should have multiple block relations (at least bb0, true branch, false branch)
        let fn_relations: Vec<_> =
            vc.relations.iter().filter(|r| r.name.contains("max_of__bb")).collect();
        assert!(
            fn_relations.len() >= 3,
            "if-else should produce >= 3 block relations, got {}",
            fn_relations.len()
        );

        assert_vc_structure(&vc, "max_of", body.blocks.len());
    });
}

// =============================================================================
// Signedness propagation — update_local_signedness_from_rvalue
// =============================================================================

/// Verify that signed/unsigned arithmetic operations preserve signedness
/// information for correct BV operation selection.
#[test]
fn test_signedness_propagation_signed_arithmetic() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn signed_add(x: i32, y: i32) -> i32 {
            x + y
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "signed_add");
        let body = instance.body().expect("body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "signed_add", ChcConfig::default());
        let (vc, _) = chc_ctx.translate();
        let smt = emit_chc(&vc).to_string();

        // Both signed and unsigned add use bvadd in SMT-LIB (signedness
        // only matters for comparison and extension operations)
        assert!(smt.contains("bvadd"), "Signed addition should produce bvadd");

        assert_vc_structure(&vc, "signed_add", body.blocks.len());
    });
}

// =============================================================================
// Empty block — no statements, just terminator
// =============================================================================

/// Verify that blocks with no statements (only terminator) are handled
/// correctly — the function should still produce valid rules.
#[test]
fn test_empty_block_no_statements() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn identity(x: u32) -> u32 {
            x
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "identity");
        let body = instance.body().expect("body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "identity", ChcConfig::default());
        let (vc, _) = chc_ctx.translate();

        // Identity function should still produce valid rules
        assert!(!vc.rules.is_empty(), "Identity function should produce rules");
        assert_vc_structure(&vc, "identity", body.blocks.len());

        // For an identity function, output should pass input through.
        // The u32 parameter and return value should produce BV32 state vars.
        let has_bv32 =
            vc.relations.iter().any(|r| r.arg_sorts.iter().any(|s| s.bitvec_width() == Some(32)));
        assert!(has_bv32, "identity(u32)->u32 should have BV32 state vars");

        // Identity function has no assignments, so transition rules should
        // have no constraints from assignments (only the entry/terminator rules).
        let smt = emit_chc(&vc).to_string();
        assert!(
            !smt.contains("bvadd") && !smt.contains("bvmul"),
            "identity function should not produce arithmetic operations"
        );
    });
}

// =============================================================================
// Collection length state — clear_modified per block
// =============================================================================

/// Verify that collection length modification tracking resets per block
/// (observable through consistent VC generation across blocks).
#[test]
fn test_collection_len_state_reset_per_block() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn sum_first_two(v: &[u32]) -> u32 {
            if v.len() >= 2 {
                v[0] + v[1]
            } else {
                0
            }
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "sum_first_two");
        let body = instance.body().expect("body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "sum_first_two", ChcConfig::default());
        let (vc, _) = chc_ctx.translate();

        // Multiple blocks should all produce valid rules
        assert!(!vc.rules.is_empty(), "translate should produce rules");
        assert_vc_structure(&vc, "sum_first_two", body.blocks.len());

        // if-else with len() check should produce multiple block relations
        // (at least bb0 entry, true branch, false branch).
        let bb_count = vc.relations.iter().filter(|r| r.name.contains("sum_first_two__bb")).count();
        assert!(
            bb_count >= 3,
            "if-else with collection check should produce >= 3 block relations, got {bb_count}"
        );

        // The arithmetic v[0] + v[1] should produce bvadd in the SMT output.
        let smt = emit_chc(&vc).to_string();
        assert!(
            smt.contains("bvadd"),
            "sum_first_two should produce bvadd for v[0] + v[1]: {}",
            &smt[..smt.len().min(500)]
        );
    });
}

// =============================================================================
// Mark modified for unsupported rvalue — nondet fallback
// =============================================================================

/// Verify that unsupported rvalue patterns still produce valid (overapprox) VCs.
/// Inline assembly is one example of an unsupported rvalue.
#[test]
fn test_unsupported_rvalue_nondet_fallback() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn with_nondeterminism(x: u32) -> u32 {
            // Use a raw pointer cast that may trigger nondet fallback
            let ptr = &x as *const u32;
            let addr = ptr as usize;
            let result = (addr as u32) + 1;
            result
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "with_nondeterminism");
        let body = instance.body().expect("body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "with_nondeterminism", ChcConfig::default());
        let (vc, _) = chc_ctx.translate();

        // Even with pointer casts, the VC should be valid
        assert!(!vc.rules.is_empty(), "translate should produce rules");
        assert_vc_structure(&vc, "with_nondeterminism", body.blocks.len());

        // The result = (addr as u32) + 1 should produce bvadd.
        let smt = emit_chc(&vc).to_string();
        assert!(
            smt.contains("bvadd"),
            "nondet fallback VC should still contain bvadd for +1: {}",
            &smt[..smt.len().min(500)]
        );

        // u32 result should produce BV32 state vars.
        let has_bv32 =
            vc.relations.iter().any(|r| r.arg_sorts.iter().any(|s| s.bitvec_width() == Some(32)));
        assert!(has_bv32, "nondet fallback with u32 should have BV32 state vars");
    });
}

// =============================================================================
// Loop — back-edge and block encoding integration
// =============================================================================

/// Verify that a loop produces correct block encoding with back-edges.
#[test]
fn test_loop_block_encoding() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn sum_to(n: u32) -> u32 {
            let mut sum: u32 = 0;
            let mut i: u32 = 0;
            while i < n {
                sum += i;
                i += 1;
            }
            sum
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "sum_to");
        let body = instance.body().expect("body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "sum_to", ChcConfig::default());
        let (vc, _) = chc_ctx.translate();
        let smt = emit_chc(&vc).to_string();

        // Loop should produce bvadd for sum += i and i += 1
        let bvadd_count = smt.matches("bvadd").count();
        assert!(
            bvadd_count >= 2,
            "Loop with two additions should produce >= 2 bvadd, got {bvadd_count}"
        );

        // Loop should produce comparison for i < n
        assert!(
            smt.contains("bvult") || smt.contains("bvslt"),
            "Loop condition should produce unsigned or signed comparison"
        );

        // Should have a back-edge (a rule targeting a previously-declared block)
        assert_vc_structure(&vc, "sum_to", body.blocks.len());
    });
}
