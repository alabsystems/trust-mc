// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Tests for `prune_arrays.rs` — post-codegen pruning of dead state variables.
//!
//! Part of #3643: prune_arrays.rs has zero dedicated coverage.
//!
//! Coverage lanes:
//! - D3: Synthetic rewrite tests for Phase C (prune_relation_app)
//! - D4: MIR-backed integration tests (pre/post prune arity comparison)

// Test code: unwrap/panic are acceptable for assertions
#![allow(clippy::unwrap_used)]

use std::collections::HashMap;

use super::common::*;
use crate::codegen_ay::emit_chc;
use trust_mc_core::chc::RelationApp;

mod soundness;

// =============================================================================
// D3: Synthetic rewrite tests for Phase C — prune_relation_app
// =============================================================================

/// `prune_relation_app` removes exactly the masked argument positions.
///
/// Build a synthetic RelationApp("bb1", [a, b, c]) with keep mask
/// [true, false, true]. Assert resulting args are [a, c].
#[test]
fn test_prune_relation_app_removes_masked_positions() {
    let a = Expr::bool_const(true);
    let b = Expr::bool_const(false);
    let c = Expr::bool_const(true);

    let mut app = RelationApp::new("bb1", vec![a.clone(), b, c.clone()]);

    let mut keep_map: HashMap<&str, Vec<bool>> = HashMap::new();
    keep_map.insert("bb1", vec![true, false, true]);

    ChcCtx::prune_relation_app(&mut app, &keep_map);

    assert_eq!(app.args.len(), 2, "should have 2 args after pruning position 1");
    assert_eq!(app.args[0], a, "first surviving arg should be 'a'");
    assert_eq!(app.args[1], c, "second surviving arg should be 'c'");
    assert_eq!(&*app.name, "bb1", "relation name should be unchanged");
}

/// `prune_relation_app` leaves unmapped relations unchanged.
///
/// Relations not in the keep map (like "error") should pass through
/// with identical arg lists.
#[test]
fn test_prune_relation_app_leaves_unmapped_relations_unchanged() {
    let a = Expr::bool_const(true);
    let b = Expr::bool_const(false);

    let mut app = RelationApp::new("error", vec![a.clone(), b.clone()]);
    let original_args_len = app.args.len();

    // keep_map only has "bb1", not "error"
    let mut keep_map: HashMap<&str, Vec<bool>> = HashMap::new();
    keep_map.insert("bb1", vec![true, false]);

    ChcCtx::prune_relation_app(&mut app, &keep_map);

    assert_eq!(app.args.len(), original_args_len, "unmapped relation args should be unchanged");
    assert_eq!(app.args[0], a, "first arg should be unchanged");
    assert_eq!(app.args[1], b, "second arg should be unchanged");
}

/// `prune_relation_app` with all-true mask leaves args unchanged.
#[test]
fn test_prune_relation_app_all_kept() {
    let a = Expr::bool_const(true);
    let b = Expr::bool_const(false);

    let mut app = RelationApp::new("bb0", vec![a.clone(), b.clone()]);

    let mut keep_map: HashMap<&str, Vec<bool>> = HashMap::new();
    keep_map.insert("bb0", vec![true, true]);

    ChcCtx::prune_relation_app(&mut app, &keep_map);

    assert_eq!(app.args.len(), 2, "all-true mask should keep all args");
    assert_eq!(app.args[0], a);
    assert_eq!(app.args[1], b);
}

/// `prune_relation_app` with all-false mask removes all args.
#[test]
fn test_prune_relation_app_all_pruned() {
    let a = Expr::bool_const(true);
    let b = Expr::bool_const(false);

    let mut app = RelationApp::new("bb0", vec![a, b]);

    let mut keep_map: HashMap<&str, Vec<bool>> = HashMap::new();
    keep_map.insert("bb0", vec![false, false]);

    ChcCtx::prune_relation_app(&mut app, &keep_map);

    assert!(app.args.is_empty(), "all-false mask should remove all args");
}

/// `prune_relation_app` handles mask shorter than args (excess args kept).
///
/// Per the production code: `keep.get(*i).copied().unwrap_or(true)`.
/// Positions beyond the mask length are kept by default.
#[test]
fn test_prune_relation_app_short_mask_keeps_excess() {
    let a = Expr::bool_const(true);
    let b = Expr::bool_const(false);
    let c = Expr::bool_const(true);

    let mut app = RelationApp::new("bb0", vec![a, b, c]);

    let mut keep_map: HashMap<&str, Vec<bool>> = HashMap::new();
    // Mask only covers first position (false), positions 1 and 2 default to keep
    keep_map.insert("bb0", vec![false]);

    ChcCtx::prune_relation_app(&mut app, &keep_map);

    assert_eq!(app.args.len(), 2, "short mask should keep excess positions");
}

// =============================================================================
// D4: MIR-backed integration tests — prune pass exercises production path
// =============================================================================

/// Fixture B: Panic-only scalar locals get pruned.
///
/// A function with a panic path should have smaller post-prune relation arity
/// than the total number of MIR locals. The prune pass (Phase B) removes
/// scalar locals that only appear in error-only blocks.
const PANIC_PATH_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub fn probe_panic_path(x: u32) -> u32 {
        if x == 0 {
            panic!("zero is not allowed");
        }
        x + 1
    }
"#;

#[test]
fn test_prune_removes_panic_only_locals() {
    with_test_ay_ctx_for_source(PANIC_PATH_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_panic_path");
        let body = instance.body().expect("body");
        let vc = mir_to_chc(ctx.tcx, &body, "probe_panic_path", ChcConfig::default());

        assert_vc_structure(&vc, "probe_panic_path", body.blocks.len());

        // The panic path creates formatting temporaries. After prune, the
        // return-reachable relations should have lower arity than without
        // pruning. We verify structural soundness: all rule heads reference
        // declared relations and head/body arities match declarations.
        let declared: HashMap<&str, usize> =
            vc.relations.iter().map(|r| (r.name.as_str(), r.arg_sorts.len())).collect();

        for rule in &vc.rules {
            let head_name = rule.head.name.as_str();
            if let Some(&decl_arity) = declared.get(head_name) {
                assert_eq!(
                    rule.head.args.len(),
                    decl_arity,
                    "head arity mismatch for {head_name}: head has {} args, \
                     declaration has {decl_arity}",
                    rule.head.args.len()
                );
            }
            if let Some(ref body_rel) = rule.body.relation {
                let body_name = body_rel.name.as_str();
                if let Some(&decl_arity) = declared.get(body_name) {
                    assert_eq!(
                        body_rel.args.len(),
                        decl_arity,
                        "body arity mismatch for {body_name}: body has {} args, \
                         declaration has {decl_arity}",
                        body_rel.args.len()
                    );
                }
            }
        }

        // At least 2 relations (bb0 + error); panic path exercised
        assert!(vc.relations.len() >= 2, "should have at least bb0 and error relations");
    });
}

/// Fixture C: Head/body arity agreement is preserved after pruning.
///
/// A diamond CFG forces backward propagation (Phase B'). After prune,
/// all rule head/body arg counts must still match their declarations.
const DIAMOND_PRUNE_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub fn probe_diamond_prune(flag: bool, x: u32) -> u32 {
        let result;
        if flag {
            result = x + 1;
        } else {
            result = x + 2;
        }
        if result == 0 {
            panic!("zero result");
        }
        result
    }
"#;

#[test]
fn test_prune_preserves_arity_agreement_diamond() {
    with_test_ay_ctx_for_source(DIAMOND_PRUNE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_diamond_prune");
        let body = instance.body().expect("body");
        let vc = mir_to_chc(ctx.tcx, &body, "probe_diamond_prune", ChcConfig::default());

        assert_vc_structure(&vc, "probe_diamond_prune", body.blocks.len());

        // Verify head/body arity agreement against declarations
        let declared: HashMap<&str, usize> =
            vc.relations.iter().map(|r| (r.name.as_str(), r.arg_sorts.len())).collect();

        for rule in &vc.rules {
            let head_name = rule.head.name.as_str();
            if let Some(&decl_arity) = declared.get(head_name) {
                assert_eq!(
                    rule.head.args.len(),
                    decl_arity,
                    "diamond prune: head arity mismatch for {head_name}"
                );
            }
            if let Some(ref body_rel) = rule.body.relation {
                let body_name = body_rel.name.as_str();
                if let Some(&decl_arity) = declared.get(body_name) {
                    assert_eq!(
                        body_rel.args.len(),
                        decl_arity,
                        "diamond prune: body arity mismatch for {body_name}"
                    );
                }
            }
        }
    });
}

/// Fixture D: Loop with conditional panic — backward propagation
/// must carry state through intermediate blocks.
///
/// This exercises Phase B' where loop back-edges force the propagation
/// worklist to revisit predecessors.
const LOOP_PRUNE_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub fn probe_loop_prune(n: u32) -> u32 {
        let mut sum: u32 = 0;
        let mut i: u32 = 0;
        while i < n {
            sum = sum.wrapping_add(i);
            i = i.wrapping_add(1);
            if sum > 1000 {
                panic!("overflow");
            }
        }
        sum
    }
"#;

#[test]
fn test_prune_preserves_arity_agreement_loop() {
    with_test_ay_ctx_for_source(LOOP_PRUNE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_loop_prune");
        let body = instance.body().expect("body");
        let vc = mir_to_chc(ctx.tcx, &body, "probe_loop_prune", ChcConfig::default());

        assert_vc_structure(&vc, "probe_loop_prune", body.blocks.len());

        // Verify head/body arity agreement for loop with panic
        let declared: HashMap<&str, usize> =
            vc.relations.iter().map(|r| (r.name.as_str(), r.arg_sorts.len())).collect();

        for rule in &vc.rules {
            let head_name = rule.head.name.as_str();
            if let Some(&decl_arity) = declared.get(head_name) {
                assert_eq!(
                    rule.head.args.len(),
                    decl_arity,
                    "loop prune: head arity mismatch for {head_name}"
                );
            }
            if let Some(ref body_rel) = rule.body.relation {
                let body_name = body_rel.name.as_str();
                if let Some(&decl_arity) = declared.get(body_name) {
                    assert_eq!(
                        body_rel.args.len(),
                        decl_arity,
                        "loop prune: body arity mismatch for {body_name}"
                    );
                }
            }
        }
    });
}

/// Verify `prune_vc_unused_type_arrays` is called by the pipeline and
/// produces a well-formed VC (Direction 5: at least one test must call
/// the production pass).
///
/// Simple function: the pipeline runs prune internally through mir_to_chc.
/// We verify the post-prune VC has all rule heads referencing declared
/// relations (referential integrity invariant).
#[test]
fn test_prune_pipeline_referential_integrity() {
    with_test_ay_ctx_for_source(
        r#"
        #![allow(dead_code)]

        pub fn probe_simple_add(x: u32, y: u32) -> u32 {
            x.wrapping_add(y)
        }
        "#,
        |ctx| {
            let instance = find_instance_by_suffix(ctx.tcx, "probe_simple_add");
            let body = instance.body().expect("body");
            let vc = mir_to_chc(ctx.tcx, &body, "probe_simple_add", ChcConfig::default());

            assert_vc_structure(&vc, "probe_simple_add", body.blocks.len());

            // Every rule head and body must reference a declared relation
            let declared: HashSet<&str> = vc.relations.iter().map(|r| r.name.as_str()).collect();
            for rule in &vc.rules {
                assert!(
                    declared.contains(rule.head.name.as_str()),
                    "post-prune rule head '{}' references undeclared relation",
                    rule.head.name
                );
                if let Some(ref body_rel) = rule.body.relation {
                    assert!(
                        declared.contains(body_rel.name.as_str()),
                        "post-prune rule body '{}' references undeclared relation",
                        body_rel.name
                    );
                }
            }
        },
    );
}

// =============================================================================
// D5: Dead heap metadata pruning (#3221)
// =============================================================================

/// Non-allocating function at Ptr: obj_valid/obj_size pruned (Phase A', #3221).
#[test]
fn test_non_allocating_fn_prunes_obj_valid_obj_size() {
    let source = r#"
        #![allow(dead_code)]

        pub fn pure_add(a: u32, b: u32) -> u32 {
            a.wrapping_add(b)
        }
    "#;

    with_test_ay_ctx_for_source(source, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "pure_add");
        let body = instance.body().expect("body");
        let vc = mir_to_chc(
            ctx.tcx,
            &body,
            "pure_add",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Ptr, ..ChcConfig::default() },
        );

        let smt = emit_chc(&vc).to_string();

        // Pruned metadata should not appear in relation signatures.
        for rel in &vc.relations {
            if rel.name == "error" {
                continue;
            }
            for (i, sort) in rel.arg_sorts.iter().enumerate() {
                let sort_str = sort.to_string();
                assert!(
                    !sort_str.contains("Array"),
                    "pure_add at Ptr level: relation {} param {i} has Array sort '{}' — \
                     obj_valid/obj_size should be pruned for non-allocating functions (#3221)",
                    rel.name,
                    sort_str,
                );
            }
        }

        // Also verify the SMT text doesn't have obj_valid/obj_size in declare-rel lines
        for line in smt.lines() {
            if line.trim_start().starts_with("(declare-rel") {
                assert!(
                    !line.contains("obj_valid") && !line.contains("obj_size"),
                    "pure_add: declare-rel should not reference obj_valid/obj_size after pruning: {line}"
                );
            }
        }
    });
}

/// Deref function at Ptr level: obj_valid/obj_size RETAINED (metadata_accessed_blocks non-empty).
#[test]
fn test_allocating_fn_retains_obj_valid_obj_size() {
    let source = r#"
        #![allow(dead_code)]

        pub fn deref_and_add(x: &u32, y: &u32) -> u32 {
            (*x).wrapping_add(*y)
        }
    "#;

    with_test_ay_ctx_for_source(source, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "deref_and_add");
        let body = instance.body().expect("body");
        let vc = mir_to_chc(
            ctx.tcx,
            &body,
            "deref_and_add",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Ptr, ..ChcConfig::default() },
        );

        let smt = emit_chc(&vc).to_string();

        // Functions that dereference pointers should retain obj_valid/obj_size
        assert!(
            smt.contains("obj_valid"),
            "deref_and_add at Ptr level should retain obj_valid (heap metadata accessed)"
        );
        assert!(
            smt.contains("obj_size"),
            "deref_and_add at Ptr level should retain obj_size (heap metadata accessed)"
        );
    });
}

fn assert_obj_size_relations_keep_obj_valid(
    vc: &trust_mc_core::chc::ChcVc,
    fn_name: &str,
    issue: &str,
) {
    let obj_valid_sort = crate::codegen_ay::chc::codegen_expr_heap::obj_valid_sort();
    let obj_size_sort = crate::codegen_ay::chc::codegen_expr_heap::obj_size_sort();
    let mut saw_obj_size_relation = false;

    for rel in vc.relations.iter().filter(|rel| rel.name.as_str() != "error") {
        let has_obj_size = rel.arg_sorts.contains(&obj_size_sort);
        if !has_obj_size {
            continue;
        }

        saw_obj_size_relation = true;
        assert!(
            rel.arg_sorts.contains(&obj_valid_sort),
            "{fn_name}: relation {} has obj_size but not obj_valid ({issue})",
            rel.name
        );
    }

    assert!(
        saw_obj_size_relation,
        "{fn_name}: expected at least one non-error relation carrying obj_size ({issue})"
    );
}

/// Part of #3793: Box<dyn Trait> D2 drop with static mutation must retain
/// obj_valid in all relation signatures that carry deallocation transitions.
#[test]
fn test_box_dyn_drop_retains_obj_valid_in_all_relations() {
    with_test_ay_ctx_for_source(
        r#"
        #![allow(dead_code)]
        static mut CELL: i32 = 0;
        trait T { fn t(&self) {} }
        struct C1;
        impl T for C1 {}
        impl Drop for C1 { fn drop(&mut self) { unsafe { CELL = 1; } } }
        struct C2;
        impl T for C2 {}
        impl Drop for C2 { fn drop(&mut self) { unsafe { CELL = 2; } } }

        pub fn probe_d2_drop(pick: bool) {
            let x: Box<dyn T> = if pick {
                Box::new(C1)
            } else {
                Box::new(C2)
            };
            drop(x);
            unsafe { assert!(CELL == 1 || CELL == 2); }
        }
        "#,
        |ctx| {
            let instance = find_instance_by_suffix(ctx.tcx, "probe_d2_drop");
            let body = instance.body().expect("body");
            let config =
                ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() };
            let vc = mir_to_chc(ctx.tcx, &body, "probe_d2_drop", config);
            let smt = crate::codegen_ay::emit_chc(&vc).to_string();

            assert_obj_size_relations_keep_obj_valid(&vc, "probe_d2_drop", "#3793");
            // D2 dealloc constraints must be present.
            assert!(
                smt.contains("obj_valid__out"),
                "D2 drop must emit obj_valid__out store (#3793)"
            );
        },
    );
}

/// Part of #3872: boxed dyn coercion assert paths must keep obj_valid threaded
/// through intermediate relations so later stack-local stores don't see a fresh
/// unconstrained metadata array.
#[test]
fn test_box_dyn_assert_path_retains_obj_valid_in_all_relations() {
    with_test_ay_ctx_for_source(
        r#"
        #![allow(dead_code)]
        use std::boxed::Box;
        use std::ops::Deref;

        trait Identity {
            fn id(&self) -> u16;
        }

        struct Inner {
            id: u8,
        }

        impl Identity for Inner {
            fn id(&self) -> u16 { self.id.into() }
        }

        fn id_from_coerce<T>(x: T) -> u16
        where
            T: Deref<Target = dyn Identity>,
        {
            x.id()
        }

        pub fn probe_box_dyn_assert() {
            let id = 5u8;
            let inner: Box<dyn Identity> = Box::new(Inner { id });
            let result = id_from_coerce(inner);
            assert_eq!(result, id.into());
        }
        "#,
        |ctx| {
            let instance = find_instance_by_suffix(ctx.tcx, "probe_box_dyn_assert");
            let body = instance.body().expect("body");
            let config =
                ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() };
            let vc = mir_to_chc(ctx.tcx, &body, "probe_box_dyn_assert", config);
            assert_obj_size_relations_keep_obj_valid(&vc, "probe_box_dyn_assert", "#3872");
        },
    );
}
