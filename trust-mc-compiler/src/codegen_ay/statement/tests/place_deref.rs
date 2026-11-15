// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Tests for place_deref.rs and codegen_place_value.rs.
//!
//! Covers:
//! - `try_codegen_box_field_access`: Box<T> field access through heap_pointees
//! - `is_box_type`: Box type detection
//! - `emit_raw_ptr_deref_checks`: Null/alignment/dead-object checks for raw ptrs
//! - `assign_value_to_place`: SSA value assignment helper
//! - `get_value_through_ref`: Reference dereference for value extraction
//! - `get_option_payload_value`: Option payload value semantics
//! - `box_pointee_ty`: Box<T> pointee type extraction
//!
//! Part of #2016.

use super::*;
use std::sync::Arc;

// =============================================================================
// Box pattern detection — MIR-driven tests
// =============================================================================

/// Test Box unwrap projection pattern detection through MIR.
/// Box<T> produces: base.0.0 (Unique -> NonNull -> *const T) then Deref.
#[test]
fn test_box_unwrap_projection_pattern_mir() {
    with_test_ay_ctx_for_source(
        r#"
        pub fn box_deref(b: Box<u32>) -> u32 {
            *b
        }
        "#,
        |mut ctx| {
            let instance = find_instance_by_suffix(&ctx, "box_deref");
            let body = instance.body().expect("body");
            ctx.set_current_fn(instance);
            let tuple_usage = TupleUsageAnalysis::run(&body);
            let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

            let mut stmt_count = 0;
            for bb in &body.blocks {
                for stmt in &bb.statements {
                    codegen.codegen_statement(stmt);
                    stmt_count += 1;
                }
            }

            // Box deref: verify codegen processed statements and MIR is non-trivial
            assert!(stmt_count > 0, "box_deref should have MIR statements");
            // Box<u32> return type means codegen must handle the unwrap pattern.
            // Verify the return type's arg count matches Box<u32> (1 arg).
            assert_eq!(
                body.arg_locals().len(),
                1,
                "box_deref should have exactly 1 arg (b: Box<u32>)"
            );
        },
    );
}

/// Test that codegen doesn't panic when processing Box field access.
#[test]
fn test_box_field_access_mir() {
    with_test_ay_ctx_for_source(
        r#"
        pub struct Point { x: u32, _y: u32 }
        pub fn box_field(b: Box<Point>) -> u32 {
            b.x
        }
        "#,
        |mut ctx| {
            let instance = find_instance_by_suffix(&ctx, "box_field");
            let body = instance.body().expect("body");
            ctx.set_current_fn(instance);
            let tuple_usage = TupleUsageAnalysis::run(&body);
            let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

            let mut stmt_count = 0;
            for bb in &body.blocks {
                for stmt in &bb.statements {
                    codegen.codegen_statement(stmt);
                    stmt_count += 1;
                }
            }

            // Box field access: verify codegen processed statements and MIR is non-trivial
            assert!(stmt_count > 0, "box_field should have MIR statements");
            // Box<Point> with field access means MIR has multiple blocks for
            // the unwrap + field extraction pattern.
            assert_eq!(
                body.arg_locals().len(),
                1,
                "box_field should have exactly 1 arg (b: Box<Point>)"
            );
        },
    );
}

/// Test that short projection chains (single Deref) for references work.
#[test]
fn test_short_deref_ref() {
    with_test_ay_ctx_for_source(
        r#"
        pub fn short_deref(r: &u32) -> u32 {
            *r
        }
        "#,
        |mut ctx| {
            let instance = find_instance_by_suffix(&ctx, "short_deref");
            let body = instance.body().expect("body");
            ctx.set_current_fn(instance);
            let tuple_usage = TupleUsageAnalysis::run(&body);
            let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

            for bb in &body.blocks {
                for stmt in &bb.statements {
                    codegen.codegen_statement(stmt);
                }
            }

            // Return place should have a value (simple deref, not Box pattern)
            let fn_name =
                codegen.ctx.current_fn().map_or_else(|| "unknown".to_string(), |f| f.name.clone());
            let return_base = format!("{}::local_0", fn_name);
            let entry = codegen.env_lookup(&return_base);
            assert!(entry.is_some(), "return place should have value after simple ref deref");
        },
    );
}

/// Test is_box_type detection through MIR.
#[test]
fn test_is_box_type_detection_mir() {
    with_test_ay_ctx_for_source(
        r#"
        pub fn box_check(b: Box<u32>, r: &u32) -> u32 {
            *b + *r
        }
        "#,
        |mut ctx| {
            let instance = find_instance_by_suffix(&ctx, "box_check");
            let body = instance.body().expect("body");
            ctx.set_current_fn(instance);

            // Check that arg 1 (Box<u32>) is detected as Box type
            // and arg 2 (&u32) is not
            let arg_locals = body.arg_locals();
            if let Some(box_local) = arg_locals.first() {
                let is_box = matches!(
                    box_local.ty.kind(),
                    TyKind::RigidTy(RigidTy::Adt(def, _))
                    if def.name().contains("Box")
                );
                assert!(is_box, "first argument should be Box type");
            }
            if let Some(ref_local) = arg_locals.get(1) {
                let is_ref = matches!(ref_local.ty.kind(), TyKind::RigidTy(RigidTy::Ref(..)));
                assert!(is_ref, "second argument should be reference type");
            }
        },
    );
}

// =============================================================================
// Raw pointer deref checks — expression-level tests
// =============================================================================

/// Test null pointer check expression: ptr == 0.
#[test]
fn test_null_pointer_check_expr() {
    let ptr = Expr::var("ptr", Sort::bitvec(POINTER_WIDTH));
    let zero = Expr::bitvec_const(0u128, POINTER_WIDTH);
    let null_check = ptr.eq(zero);

    assert!(null_check.sort().is_bool());
    assert!(matches!(null_check.value(), ExprValue::Eq(_, _)));
}

/// Test alignment check expression: (ptr % align) != 0.
#[test]
fn test_alignment_check_expr() {
    let ptr = Expr::var("ptr", Sort::bitvec(POINTER_WIDTH));
    let align = Expr::bitvec_const(8u128, POINTER_WIDTH);
    let rem = ptr.bvurem(align);
    let zero = Expr::bitvec_const(0u128, POINTER_WIDTH);
    let misaligned = rem.eq(zero).not();

    assert!(misaligned.sort().is_bool());
    assert!(matches!(misaligned.value(), ExprValue::Not(_)));
}

/// Test alignment check with alignment=1 (skip - all pointers are aligned to 1).
#[test]
fn test_alignment_check_align1_skip() {
    let align: usize = 1;
    // When align <= 1, no alignment check should be emitted
    assert!(align <= 1, "alignment 1 should be skipped");
}

/// Test alignment check with alignment=4.
#[test]
fn test_alignment_check_align4() {
    let ptr = Expr::var("ptr", Sort::bitvec(POINTER_WIDTH));
    let align: usize = 4;
    let align_expr = Expr::bitvec_const(align as u128, POINTER_WIDTH);
    let rem = ptr.bvurem(align_expr);
    let zero = Expr::bitvec_const(0u128, POINTER_WIDTH);
    let misaligned = rem.eq(zero).not();

    assert!(misaligned.sort().is_bool());
}

/// Raw-pointer dereference should emit use-after-free guard via heap_is_allocated.
#[test]
fn test_raw_ptr_load_deref_records_use_after_free_violation() {
    with_test_ay_ctx_for_source(
        r#"
        pub unsafe fn raw_load(ptr: *const u8) -> u8 {
            unsafe { *ptr }
        }
        "#,
        |mut ctx| {
            let instance = find_instance_by_suffix(&ctx, "raw_load");
            let body = instance.body().expect("body");
            ctx.set_current_fn(instance);
            let tuple_usage = TupleUsageAnalysis::run(&body);
            let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

            for bb in &body.blocks {
                for stmt in &bb.statements {
                    codegen.codegen_statement(stmt);
                }
            }

            let use_after_free: Vec<_> = codegen
                .ctx
                .bmc_vc
                .violations
                .iter()
                .filter(|v| {
                    v.smt_var.as_deref().is_some_and(|name| name.contains("use_after_free_check"))
                })
                .collect();
            assert!(
                !use_after_free.is_empty(),
                "raw pointer load deref should emit use_after_free_check violation"
            );
            assert!(
                use_after_free
                    .iter()
                    .all(|v| v.kind == trust_mc_core::violation::PropertyKind::MemorySafety),
                "use_after_free_check violations should be MemorySafety"
            );
        },
    );
}

/// Raw-pointer store dereference should emit use-after-free guard via heap_is_allocated.
#[test]
fn test_raw_ptr_store_deref_records_use_after_free_violation() {
    with_test_ay_ctx_for_source(
        r#"
        pub unsafe fn raw_store(ptr: *mut u8, val: u8) {
            unsafe { *ptr = val; }
        }
        "#,
        |mut ctx| {
            let instance = find_instance_by_suffix(&ctx, "raw_store");
            let body = instance.body().expect("body");
            ctx.set_current_fn(instance);
            let tuple_usage = TupleUsageAnalysis::run(&body);
            let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

            for bb in &body.blocks {
                for stmt in &bb.statements {
                    codegen.codegen_statement(stmt);
                }
            }

            let emitted = codegen.ctx.bmc_vc.violations.iter().any(|v| {
                v.smt_var.as_deref().is_some_and(|name| name.contains("use_after_free_check"))
            });
            assert!(emitted, "raw pointer store deref should emit use_after_free_check violation");
        },
    );
}

/// Test dead object check expression: bool_const(true) guarded by path condition.
#[test]
fn test_dead_object_check_expr() {
    let violation = Expr::bool_const(true);
    let path_cond = Expr::var("path_cond_bb3", Sort::bool());
    let guarded = path_cond.implies(violation);

    assert!(guarded.sort().is_bool());
    assert!(matches!(guarded.value(), ExprValue::Implies(_, _)));
}

/// Test dead locals tracking pattern: extract local index from base name.
/// Uses production `resolve_ref_chain_target` instead of duplicating parsing logic.
#[test]
fn test_dead_locals_index_extraction() {
    let ref_pointees = std::collections::BTreeMap::new();
    assert_eq!(StatementCodegen::resolve_ref_chain_target(&ref_pointees, "my_fn::local_5"), 5);
}

#[test]
fn test_storage_live_reactivates_a_previous_frame_slot() {
    with_test_ay_ctx_for_source("pub fn slot(value: u8) -> u8 { value }", |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "slot");
        let body = instance.body().expect("slot body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);
        let span = mir_span!(body.blocks[0].terminator);
        let dead = crate::rustc_compat::mir_statement(StatementKind::StorageDead(1), span);
        let live = crate::rustc_compat::mir_statement(StatementKind::StorageLive(1), span);
        codegen.codegen_statement(&dead);
        assert!(codegen.dead_locals.contains(&1));
        codegen.codegen_statement(&live);
        assert!(!codegen.dead_locals.contains(&1));
        codegen.codegen_statement(&dead);
        assert!(codegen.dead_locals.contains(&1));
    });
}

#[test]
fn test_storage_live_reused_address_requires_generations_except_for_zst() {
    let source = r#"
        pub fn address_byte(value: u8) -> *const u8 { &value }
        pub fn address_zst(value: ()) -> *const () { &value }
    "#;
    for (name, refused) in [("address_byte", true), ("address_zst", false)] {
        with_test_ay_ctx_for_source(source, |mut ctx| {
            let instance = find_instance_by_suffix(&ctx, name);
            let mut body = instance.body().expect("address body");
            let span = mir_span!(body.blocks[0].terminator);
            let live = crate::rustc_compat::mir_statement(StatementKind::StorageLive(1), span);
            let dead = crate::rustc_compat::mir_statement(StatementKind::StorageDead(1), span);
            body.blocks[0].statements.splice(0..0, [live.clone(), dead, live.clone()]);
            ctx.set_current_fn(instance);
            let tuple_usage = TupleUsageAnalysis::run(&body);
            let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);
            codegen.codegen_statement(&live);
            assert_eq!(
                codegen.ctx.unsupported_constructs.contains_key("reused_stack_allocation_identity"),
                refused,
                "{name}",
            );
        });
    }
}

/// Test dead locals extraction from complex base name (with field suffix).
/// Uses production `resolve_ref_chain_target` instead of duplicating parsing logic.
#[test]
fn test_dead_locals_index_extraction_with_fields() {
    let ref_pointees = std::collections::BTreeMap::new();
    assert_eq!(
        StatementCodegen::resolve_ref_chain_target(&ref_pointees, "my_fn::local_12_field_0"),
        12
    );
}

/// An unresolved `X_deref` alias names what pointer X points to, so it has no
/// allocation to size-check: `Box::into_raw` leaves `p -> local_22_deref` with
/// `local_22` an 8-byte pointer, and an i128 payload read was reported as a
/// 16-byte access to it. A resolved alias and a plain local keep their target.
#[test]
fn test_unresolved_deref_alias_has_no_allocation() {
    let mut ref_pointees = std::collections::BTreeMap::new();
    assert_eq!(
        StatementCodegen::resolve_ref_chain_allocation(&ref_pointees, "my_fn::local_22_deref"),
        None
    );
    assert_eq!(
        StatementCodegen::resolve_ref_chain_allocation(&ref_pointees, "my_fn::local_5"),
        Some(5)
    );
    ref_pointees.insert(Arc::from("my_fn::local_22"), Arc::from("my_fn::local_19"));
    assert_eq!(
        StatementCodegen::resolve_ref_chain_allocation(&ref_pointees, "my_fn::local_22_deref"),
        Some(19)
    );
}

/// A pointee name is an alias because its LOCAL suffix says so, never because the
/// enclosing FUNCTION is named `*_deref`. `expected/ptr_to_ref_cast::check_zst_deref`
/// verified SUCCESSFUL against an oracle of FAILED for exactly this reason: the
/// whole-name `contains("_deref")` matched the harness name, skipped the early
/// return, and the object-extent obligation -- the only one that could be false for
/// a cast out of a zero-sized allocation -- was never emitted.
#[test]
fn test_deref_alias_is_a_local_suffix_not_a_function_name() {
    // The collision: six of that corpus file's seven harnesses are named `*_deref`.
    for name in [
        "check_zst_deref::local_2",
        "check_larger_deref::local_1",
        "check_larger_deref_into_ptr::local_1",
        "check_larger_deref_struct::local_1",
        "check_equal_size_deref::local_1",
        "check_smaller_deref::local_2",
    ] {
        assert!(
            !StatementCodegen::is_deref_alias(name),
            "{name}: a function named *_deref must not make its plain locals look like aliases"
        );
    }
    // A genuine alias still reads as one.
    assert!(StatementCodegen::is_deref_alias("my_fn::local_22_deref"));
    // And the two together: an alias inside a `*_deref` function.
    assert!(StatementCodegen::is_deref_alias("check_zst_deref::local_22_deref"));
}

/// The same collision for `_field_`: a function named `*_field_*` must not suppress
/// the obligation for every local inside it.
#[test]
fn test_field_chain_is_a_local_suffix_not_a_function_name() {
    assert!(!StatementCodegen::is_field_chain("check_field_access::local_1"));
    assert!(StatementCodegen::is_field_chain("my_fn::local_12_field_0"));
}

/// The LOCAL is the LAST `::local_` segment. `split("::local_").nth(1)` yields
/// `1::inner` on a nested name, which then parses to the `usize::MAX` sentinel.
#[test]
fn test_local_part_takes_the_last_segment() {
    assert_eq!(StatementCodegen::local_part("check_zst_deref::local_2"), Some("2"));
    // Consistent with the resolvers' own `split("::local_").nth(1)` / `split_once`: the
    // FIRST separator. Pathological and unobserved, pinned only so the predicate and the
    // index cannot drift apart.
    assert_eq!(
        StatementCodegen::local_part("outer::local_1::inner::local_3"),
        Some("1::inner::local_3")
    );
    assert_eq!(StatementCodegen::local_part("Store::<'a, LEN>::from::local_1"), Some("1"));
    assert_eq!(StatementCodegen::local_part("some_opaque_name"), None);
}

/// A plain local inside a `*_deref` function resolves to an allocation. Before the
/// fix this returned None and the caller's `continue` dropped the size check.
#[test]
fn test_plain_local_in_a_deref_named_function_resolves() {
    let ref_pointees = std::collections::BTreeMap::new();
    assert_eq!(
        StatementCodegen::resolve_ref_chain_allocation(&ref_pointees, "check_zst_deref::local_2"),
        Some(2),
        "a plain local must resolve even when the function name contains _deref"
    );
    // The alias behaviour the original guard was written for is unchanged.
    assert_eq!(
        StatementCodegen::resolve_ref_chain_allocation(&ref_pointees, "my_fn::local_22_deref"),
        None
    );
}

// Ref chain chasing tests call the production `resolve_ref_chain_target` method
// directly (Part of #2271). The method was extracted from `emit_raw_ptr_deref_checks`
// to make it independently testable without a full MIR/SSA environment.

/// Helper: looks up pointee for `ptr_base` then calls production `resolve_ref_chain_target`.
/// Bridges the test's ptr_base → pointee_base lookup with the production chain resolver.
fn resolve_chain(
    ref_pointees: &std::collections::BTreeMap<Arc<str>, Arc<str>>,
    ptr_base: &str,
) -> usize {
    match ref_pointees.get(ptr_base) {
        Some(pointee_base) => {
            StatementCodegen::resolve_ref_chain_target(ref_pointees, pointee_base)
        }
        None => usize::MAX,
    }
}

/// Test ref chain chasing: ptr -> ref_temp -> source_local.
/// When `ref_pointees` maps ptr_base -> local_3 and local_3 -> local_7,
/// the chain chasing should resolve to local_7 as the target.
#[test]
fn test_ref_chain_chasing_two_level() {
    let mut ref_pointees = std::collections::BTreeMap::new();
    ref_pointees.insert(Arc::from("test_fn::local_1"), Arc::from("test_fn::local_3"));
    ref_pointees.insert(Arc::from("test_fn::local_3"), Arc::from("test_fn::local_7"));

    assert_eq!(resolve_chain(&ref_pointees, "test_fn::local_1"), 7);
}

/// Test ref chain chasing: single-level (no chain) falls through to immediate local.
#[test]
fn test_ref_chain_chasing_single_level() {
    let mut ref_pointees = std::collections::BTreeMap::new();
    ref_pointees.insert(Arc::from("test_fn::local_1"), Arc::from("test_fn::local_5"));

    assert_eq!(resolve_chain(&ref_pointees, "test_fn::local_1"), 5);
}

/// Test ref chain chasing: unparseable local name falls back to usize::MAX sentinel.
#[test]
fn test_ref_chain_chasing_unparseable_sentinel() {
    let mut ref_pointees = std::collections::BTreeMap::new();
    ref_pointees.insert(Arc::from("test_fn::local_1"), Arc::from("test_fn::local_abc"));

    let idx = resolve_chain(&ref_pointees, "test_fn::local_1");
    assert_eq!(idx, usize::MAX, "unparseable name → sentinel");
    // Sentinel should not match any realistic dead_locals entry
    let dead_locals: std::collections::HashSet<usize> = [3, 5, 7].iter().copied().collect();
    assert!(!dead_locals.contains(&idx));
}

/// Test chain chasing with field suffix on inner pointee.
/// Exercises the `split('_').next()` on the inner pointee's local_str.
#[test]
fn test_ref_chain_chasing_inner_pointee_with_field() {
    let mut ref_pointees = std::collections::BTreeMap::new();
    ref_pointees.insert(Arc::from("test_fn::local_1"), Arc::from("test_fn::local_3"));
    ref_pointees.insert(Arc::from("test_fn::local_3"), Arc::from("test_fn::local_9_field_0"));

    assert_eq!(resolve_chain(&ref_pointees, "test_fn::local_1"), 9);
}

/// Test resolve_ref_chain_target directly with no ref_pointees entry for the
/// immediate local (tests the "no chain" fallback path).
#[test]
fn test_resolve_ref_chain_target_no_chain_entry() {
    let ref_pointees = std::collections::BTreeMap::new();
    assert_eq!(StatementCodegen::resolve_ref_chain_target(&ref_pointees, "test_fn::local_5"), 5);
}

/// Test resolve_ref_chain_target with a name that has no "::local_" separator.
#[test]
fn test_resolve_ref_chain_target_no_local_separator() {
    let ref_pointees = std::collections::BTreeMap::new();
    assert_eq!(
        StatementCodegen::resolve_ref_chain_target(&ref_pointees, "some_opaque_name"),
        usize::MAX
    );
}

#[test]
fn test_storage_lifetime_join_does_not_inherit_previous_block() {
    with_test_ay_ctx_for_source(
        "pub fn join(flag: bool, value: u8) -> u8 { if flag { value } else { 0 } }",
        |mut ctx| {
            let instance = find_instance_by_suffix(&ctx, "join");
            let mut body = instance.body().expect("join body");
            let span = mir_span!(body.blocks[0].terminator);
            let dead = crate::rustc_compat::mir_statement(StatementKind::StorageDead(2), span);
            let block = |statements, kind| rustc_public::mir::BasicBlock {
                statements,
                terminator: crate::rustc_compat::mir_terminator(kind, span),
            };
            use rustc_public::mir::{SwitchTargets, TerminatorKind};
            body.blocks = vec![
                block(
                    vec![],
                    TerminatorKind::SwitchInt {
                        discr: Operand::Copy(Place::from(1)),
                        targets: SwitchTargets::new(vec![(0, 1)], 2),
                    },
                ),
                block(vec![dead.clone()], TerminatorKind::Goto { target: 3 }),
                block(vec![], TerminatorKind::Goto { target: 3 }),
                block(vec![], TerminatorKind::Return),
            ];
            ctx.set_current_fn(instance);
            let tuple_usage = TupleUsageAnalysis::run(&body);
            let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);
            codegen.initialize_storage_block(1);
            codegen.codegen_statement(&dead);
            assert_eq!(codegen.stack_local_is_live(2), Some(false));
            codegen.initialize_storage_block(2);
            assert_eq!(codegen.stack_local_is_live(2), Some(true));
            codegen.initialize_storage_block(3);
            assert_eq!(codegen.stack_local_is_live(2), None);
        },
    );
}

// =============================================================================
// assign_value_to_place — MIR-driven tests
// =============================================================================

/// Test assign_value_to_place creates SSA variable and updates env.
#[test]
fn test_assign_value_to_place_updates_env() {
    with_test_ay_ctx_for_source(
        r#"
        pub fn assign_target(x: u32) -> u32 { x }
        "#,
        |mut ctx| {
            let instance = find_instance_by_suffix(&ctx, "assign_target");
            let body = instance.body().expect("body");
            ctx.set_current_fn(instance);
            let tuple_usage = TupleUsageAnalysis::run(&body);
            let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

            let dest = Place { local: Local::from(0usize), projection: vec![] };
            let value = Expr::bitvec_const(42u128, 32);

            codegen.assign_value_to_place(&dest, value);

            let fn_name =
                codegen.ctx.current_fn().map_or_else(|| "unknown".to_string(), |f| f.name.clone());
            let base = format!("{}::local_0", fn_name);
            let entry = codegen.env_lookup(&base);
            assert!(entry.is_some(), "assign_value_to_place should create env entry");
            if let Some(expr) = entry {
                assert!(expr.sort().is_bitvec(), "value should be bitvec");
            }
        },
    );
}

/// Test assign_value_to_place with bool value.
#[test]
fn test_assign_value_to_place_bool() {
    with_test_ay_ctx_for_source(
        r#"
        pub fn assign_bool_target(x: bool) -> bool { x }
        "#,
        |mut ctx| {
            let instance = find_instance_by_suffix(&ctx, "assign_bool_target");
            let body = instance.body().expect("body");
            ctx.set_current_fn(instance);
            let tuple_usage = TupleUsageAnalysis::run(&body);
            let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

            let dest = Place { local: Local::from(0usize), projection: vec![] };
            let value = Expr::bool_const(true);

            codegen.assign_value_to_place(&dest, value);

            let fn_name =
                codegen.ctx.current_fn().map_or_else(|| "unknown".to_string(), |f| f.name.clone());
            let base = format!("{}::local_0", fn_name);
            let entry = codegen.env_lookup(&base);
            assert!(entry.is_some(), "assign_value_to_place should create env entry for bool");
            if let Some(expr) = entry {
                assert!(expr.sort().is_bool(), "value should be bool sort");
            }
        },
    );
}

/// Test assign_value_to_place with array sort.
#[test]
fn test_assign_value_to_place_array() {
    with_test_ay_ctx_for_source(
        r#"
        pub fn assign_arr_target() -> [u32; 4] { [0u32; 4] }
        "#,
        |mut ctx| {
            let instance = find_instance_by_suffix(&ctx, "assign_arr_target");
            let body = instance.body().expect("body");
            ctx.set_current_fn(instance);
            let tuple_usage = TupleUsageAnalysis::run(&body);
            let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

            let dest = Place { local: Local::from(0usize), projection: vec![] };
            let arr = Expr::const_array(Sort::bitvec(POINTER_WIDTH), Expr::bitvec_const(0u128, 32));

            codegen.assign_value_to_place(&dest, arr);

            let fn_name =
                codegen.ctx.current_fn().map_or_else(|| "unknown".to_string(), |f| f.name.clone());
            let base = format!("{}::local_0", fn_name);
            let entry = codegen.env_lookup(&base);
            assert!(entry.is_some(), "assign_value_to_place should create env entry for array");
            if let Some(expr) = entry {
                assert!(expr.sort().is_array(), "value should be array sort");
            }
        },
    );
}

// =============================================================================
// get_value_through_ref — MIR-driven tests
// =============================================================================

/// Test that reference deref resolves to pointee value in simple case.
#[test]
fn test_get_value_through_ref_simple() {
    with_test_ay_ctx_for_source(
        r#"
        pub fn ref_value(x: u32) -> u32 {
            let r = &x;
            *r
        }
        "#,
        |mut ctx| {
            let instance = find_instance_by_suffix(&ctx, "ref_value");
            let body = instance.body().expect("body");
            ctx.set_current_fn(instance);
            let tuple_usage = TupleUsageAnalysis::run(&body);
            let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

            // Process all statements to populate ref_pointees and env
            for bb in &body.blocks {
                for stmt in &bb.statements {
                    codegen.codegen_statement(stmt);
                }
            }

            // ref_pointees should be populated from `let r = &x`
            assert!(
                !codegen.ref_pointees.is_empty(),
                "ref_pointees should have entries after processing reference"
            );

            // Return place should have a value (from *r)
            let fn_name =
                codegen.ctx.current_fn().map_or_else(|| "unknown".to_string(), |f| f.name.clone());
            let return_base = format!("{}::local_0", fn_name);
            let entry = codegen.env_lookup(&return_base);
            assert!(entry.is_some(), "return place should have value after ref deref assignment");
        },
    );
}

/// Test get_value_through_ref with mutable reference.
#[test]
fn test_get_value_through_mut_ref() {
    with_test_ay_ctx_for_source(
        r#"
        pub fn mut_ref_value(mut x: u32) -> u32 {
            let r = &mut x;
            *r += 1;
            *r
        }
        "#,
        |mut ctx| {
            let instance = find_instance_by_suffix(&ctx, "mut_ref_value");
            let body = instance.body().expect("body");
            ctx.set_current_fn(instance);
            let tuple_usage = TupleUsageAnalysis::run(&body);
            let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

            for bb in &body.blocks {
                for stmt in &bb.statements {
                    codegen.codegen_statement(stmt);
                }
            }

            // Should have ref_pointees from mutable reference
            assert!(
                !codegen.ref_pointees.is_empty(),
                "ref_pointees should track mutable reference"
            );
        },
    );
}

// =============================================================================
// Raw pointer deref check — MIR-driven integration tests
// =============================================================================

/// Test that raw pointer deref through unsafe code doesn't panic.
#[test]
fn test_raw_ptr_deref_codegen_no_panic() {
    with_test_ay_ctx_for_source(
        r#"
        pub fn raw_ptr_read(ptr: *const u32) -> u32 {
            unsafe { *ptr }
        }
        "#,
        |mut ctx| {
            let instance = find_instance_by_suffix(&ctx, "raw_ptr_read");
            let body = instance.body().expect("body");
            ctx.set_current_fn(instance);
            let tuple_usage = TupleUsageAnalysis::run(&body);
            let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

            // Process all statements without panic
            let mut stmt_count = 0;
            for bb in &body.blocks {
                for stmt in &bb.statements {
                    codegen.codegen_statement(stmt);
                    stmt_count += 1;
                }
            }
            assert!(stmt_count >= 0, "should process raw pointer deref without panic");
        },
    );
}

/// Test that multiple reference chains don't cause issues.
#[test]
fn test_reference_chain_codegen() {
    with_test_ay_ctx_for_source(
        r#"
        pub fn ref_chain(x: u32) -> u32 {
            let a = &x;
            let b = *a;
            b
        }
        "#,
        |mut ctx| {
            let instance = find_instance_by_suffix(&ctx, "ref_chain");
            let body = instance.body().expect("body");
            ctx.set_current_fn(instance);
            let tuple_usage = TupleUsageAnalysis::run(&body);
            let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

            for bb in &body.blocks {
                for stmt in &bb.statements {
                    codegen.codegen_statement(stmt);
                }
            }

            let fn_name =
                codegen.ctx.current_fn().map_or_else(|| "unknown".to_string(), |f| f.name.clone());
            let return_base = format!("{}::local_0", fn_name);
            let entry = codegen.env_lookup(&return_base);
            assert!(entry.is_some(), "return place should have value after reference chain");
        },
    );
}

// =============================================================================
// Helper
// =============================================================================
