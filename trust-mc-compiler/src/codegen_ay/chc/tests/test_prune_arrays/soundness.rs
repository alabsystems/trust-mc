// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Additional soundness coverage for `prune_arrays.rs`.
//!
//! Part of #3643: cover write-only type arrays, vtable liveness, and the
//! defensive worklist-bound lane without growing `test_prune_arrays.rs`
//! beyond the file-size limit.

// Test code: unwrap/panic are acceptable for assertions
#![allow(clippy::unwrap_used)]

use std::collections::{HashMap, VecDeque};

use super::super::common::*;
use crate::codegen_ay::emit_chc;
use trust_mc_core::chc::{ChcVc, RelationApp};

fn assert_relation_apps_match_declarations(vc: &ChcVc, fn_name: &str) {
    let declared: HashMap<&str, usize> =
        vc.relations.iter().map(|rel| (rel.name.as_str(), rel.arg_sorts.len())).collect();

    for rule in &vc.rules {
        let head_name = rule.head.name.as_str();
        if let Some(&decl_arity) = declared.get(head_name) {
            assert_eq!(
                rule.head.args.len(),
                decl_arity,
                "{fn_name}: head arity mismatch for {head_name}"
            );
        }
        if let Some(body_rel) = &rule.body.relation {
            let body_name = body_rel.name.as_str();
            if let Some(&decl_arity) = declared.get(body_name) {
                assert_eq!(
                    body_rel.args.len(),
                    decl_arity,
                    "{fn_name}: body arity mismatch for {body_name}"
                );
            }
        }
    }
}

fn max_non_error_relation_arity(vc: &ChcVc) -> usize {
    vc.relations
        .iter()
        .filter(|rel| rel.name != "error")
        .map(|rel| rel.arg_sorts.len())
        .max()
        .unwrap_or(0)
}

fn relation_app_contains_var_fragment(app: &RelationApp, needle: &str) -> bool {
    app.args.iter().any(|arg| {
        constraint_tree_contains(
            arg,
            &|expr| matches!(expr.value(), ExprValue::Var { name } if name.contains(needle)),
        )
    })
}

fn relation_app_contains_exact_var(app: &RelationApp, needle: &str) -> bool {
    app.args.iter().any(|arg| {
        constraint_tree_contains(
            arg,
            &|expr| matches!(expr.value(), ExprValue::Var { name } if name.as_str() == needle),
        )
    })
}

fn vc_relation_apps_contain_exact_var(vc: &ChcVc, needle: &str) -> bool {
    vc.rules.iter().any(|rule| {
        relation_app_contains_exact_var(&rule.head, needle)
            || rule
                .body
                .relation
                .as_ref()
                .is_some_and(|rel| relation_app_contains_exact_var(rel, needle))
    })
}

fn observed_nonlocal_worklist_iterations(
    chc_ctx: &ChcCtx<'_, '_>,
) -> (usize, usize, usize, usize, usize) {
    let block_count = chc_ctx.state_var_mgr.live_state_indices.len();
    let array_names: Vec<&str> = chc_ctx
        .heap_state
        .type_arrays
        .values()
        .map(|(name, _)| name.as_ref())
        .chain(chc_ctx.heap_state.region_arrays.values().map(|(name, _)| name.as_ref()))
        .collect();

    let successors: Vec<Vec<usize>> = chc_ctx
        .body
        .blocks
        .iter()
        .map(|block| ChcCtx::block_successors(&block.terminator.kind))
        .collect();
    let mut predecessors: Vec<Vec<usize>> = vec![vec![]; block_count];
    for (bb, succs) in successors.iter().enumerate() {
        for &succ in succs {
            if succ < block_count {
                predecessors[succ].push(bb);
            }
        }
    }

    let max_preds = predecessors.iter().map(|preds| preds.len()).max().unwrap_or(0);
    let max_iters = block_count * array_names.len() * (max_preds + 1) + block_count;
    let mut ta_live: Vec<HashSet<usize>> = vec![HashSet::new(); block_count];
    for (arr_idx, arr_name) in array_names.iter().enumerate() {
        let read_blocks = chc_ctx.heap_state.read_used_type_arrays.get(*arr_name);
        let write_blocks = chc_ctx.heap_state.write_used_type_arrays.get(*arr_name);
        for (bb, bb_live) in ta_live.iter_mut().enumerate() {
            let read_here = read_blocks.is_some_and(|bbs| bbs.contains(&bb));
            let write_here = write_blocks.is_some_and(|bbs| bbs.contains(&bb));
            if read_here || write_here {
                bb_live.insert(arr_idx);
            }
        }
    }

    let mut worklist: VecDeque<usize> = (0..block_count).collect();
    let mut iterations = 0usize;
    while let Some(bb) = worklist.pop_front() {
        iterations += 1;
        for &succ in &successors[bb] {
            if succ >= block_count {
                continue;
            }
            let succ_live: Vec<usize> = ta_live[succ].iter().copied().collect();
            for arr_idx in succ_live {
                if ta_live[bb].insert(arr_idx) {
                    for &pred in &predecessors[bb] {
                        worklist.push_back(pred);
                    }
                }
            }
        }
    }

    (iterations, max_iters, block_count, array_names.len(), max_preds)
}

/// Fixture E: a write-only pointee creates `_mem_u32` state that Phase A can prune.
const WRITE_ONLY_REF_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub fn probe_write_only_ref(ptr: &mut u32, y: u32) -> u32 {
        *ptr = y;
        7
    }
"#;

/// Fixture F: dyn-dispatch source with a non-dispatch branch.
const DYN_DISPATCH_PRUNE_SOURCE: &str = r#"
    #![allow(dead_code)]

    trait Animal {
        fn speak(&self) -> u32;
    }

    struct Dog;
    impl Animal for Dog {
        fn speak(&self) -> u32 { 1 }
    }

    pub fn probe_dyn_dispatch_prune(flag: bool) -> u32 {
        let dog = Dog;
        let dyn_ref: &dyn Animal = &dog;
        let result;
        if flag {
            result = dyn_ref.speak();
        } else {
            result = 0;
        }
        result
    }
"#;

/// Fixture G: loop + slice reads exercise the per-block non-local liveness worklist.
const LOOP_SLICE_PRUNE_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub fn probe_loop_slice_prune(v: &[u32], n: usize) -> u32 {
        let mut i: usize = 0;
        let mut acc: u32 = 0;
        while i < n && i < v.len() {
            acc = acc.wrapping_add(v[i]);
            i += 1;
        }
        if n > 16 {
            panic!("too large");
        }
        acc
    }
"#;

/// Fixture H: wrong-size dealloc after a store must keep obj_valid and obj_size
/// together across the dealloc transition's source relation.
const DEALLOC_SIZE_MISMATCH_PRUNE_SOURCE: &str = r#"
    #![allow(dead_code)]

    use std::alloc::{Layout, alloc, dealloc};

    pub unsafe fn probe_dealloc_size_mismatch_prune() {
        let layout_alloc = Layout::from_size_align(64, 8).unwrap();
        let ptr = unsafe { alloc(layout_alloc) };
        if !ptr.is_null() {
            unsafe { *ptr = 42; }
            let layout_dealloc = Layout::from_size_align(32, 8).unwrap();
            unsafe { dealloc(ptr, layout_dealloc); }
        }
    }
"#;

#[test]
fn test_prune_phase_a_removes_write_only_type_arrays_from_relation_apps() {
    with_test_ay_ctx_for_source(WRITE_ONLY_REF_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_write_only_ref");
        let body = instance.body().expect("body");
        let fn_name = "probe_write_only_ref";
        let mem_cfg =
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() };
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, fn_name, mem_cfg);
        let arr_name = names::mem_array_name(fn_name, "u32");
        let out_name = format!("{arr_name}__out");

        chc_ctx.declare_block_relations();
        assert!(
            chc_ctx.state_var_index_by_name(arr_name.as_ref()).is_some(),
            "{fn_name}: expected predeclared write-only type array {arr_name}"
        );
        chc_ctx.declare_error_relation();
        chc_ctx.emit_entry_rule();
        chc_ctx.generate_transition_rules();

        let pre_prune_max_arity = max_non_error_relation_arity(&chc_ctx.vc);
        assert!(
            vc_relation_apps_contain_exact_var(&chc_ctx.vc, arr_name.as_ref())
                || vc_relation_apps_contain_exact_var(&chc_ctx.vc, &out_name),
            "{fn_name}: pre-prune relation apps should carry {arr_name}"
        );

        chc_ctx.prune_vc_unused_type_arrays();

        let post_prune_max_arity = max_non_error_relation_arity(&chc_ctx.vc);
        assert!(
            post_prune_max_arity < pre_prune_max_arity,
            "{fn_name}: write-only type array pruning should reduce relation arity \
             ({pre_prune_max_arity} -> {post_prune_max_arity})"
        );
        assert!(
            !vc_relation_apps_contain_exact_var(&chc_ctx.vc, arr_name.as_ref()),
            "{fn_name}: pruned relation apps should not carry input {arr_name}"
        );
        assert!(
            !vc_relation_apps_contain_exact_var(&chc_ctx.vc, &out_name),
            "{fn_name}: pruned relation apps should not carry output {out_name}"
        );
        assert!(
            chc_ctx.vc.vars().iter().any(|var| var.name.as_ref() == arr_name.as_ref()),
            "{fn_name}: declare-var for {arr_name} must remain after pruning"
        );
        assert_relation_apps_match_declarations(&chc_ctx.vc, fn_name);
    });
}

#[test]
fn test_prune_dealloc_size_mismatch_keeps_obj_valid_with_obj_size() {
    with_test_ay_ctx_for_source(DEALLOC_SIZE_MISMATCH_PRUNE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_dealloc_size_mismatch_prune");
        let body = instance.body().expect("body");
        let vc = mir_to_chc(
            ctx.tcx,
            &body,
            "probe_dealloc_size_mismatch_prune",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Ptr, ..ChcConfig::default() },
        );

        assert_relation_apps_match_declarations(&vc, "probe_dealloc_size_mismatch_prune");

        let smt = emit_chc(&vc).to_string();
        // Co-pruning guard: any declare-rel with obj_size must also have obj_valid.
        for line in smt.lines() {
            let trimmed = line.trim();
            if trimmed.starts_with("(declare-rel") && trimmed.contains("obj_size") {
                assert!(
                    trimmed.contains("obj_valid"),
                    "size-mismatch dealloc relation lost obj_valid after pruning (#3841): {trimmed}"
                );
            }
        }
        // Primary soundness check: obj_valid must survive pruning at Ptr level
        // for use-after-free detection. obj_size may be pruned if dealloc
        // transitions don't reference it (legitimate pruning behavior).
        assert!(
            smt.contains("obj_valid"),
            "size-mismatch dealloc must retain obj_valid at Ptr level (#3841)"
        );
        assert!(
            smt.contains("obj_valid__out"),
            "size-mismatch dealloc transition must emit obj_valid__out (#3841)"
        );
    });
}

#[test]
fn test_prune_keeps_vtable_state_vars_live_in_all_relation_apps() {
    with_test_ay_ctx_for_source(DYN_DISPATCH_PRUNE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_dyn_dispatch_prune");
        let body = instance.body().expect("body");
        let vc = mir_to_chc(ctx.tcx, &body, "probe_dyn_dispatch_prune", ChcConfig::default());

        assert_vc_structure(&vc, "probe_dyn_dispatch_prune", body.blocks.len());
        assert!(
            vc.vars().iter().any(|var| var.name.contains("__vtable_sv_")),
            "probe_dyn_dispatch_prune: expected predeclared vtable state vars"
        );

        for rule in &vc.rules {
            if rule.head.name != "error" {
                assert!(
                    relation_app_contains_var_fragment(&rule.head, "__vtable_sv_"),
                    "probe_dyn_dispatch_prune: head relation '{}' lost vtable state",
                    rule.head.name
                );
            }
            if let Some(body_rel) = &rule.body.relation {
                assert!(
                    relation_app_contains_var_fragment(body_rel, "__vtable_sv_"),
                    "probe_dyn_dispatch_prune: body relation '{}' lost vtable state",
                    body_rel.name
                );
            }
        }

        assert_relation_apps_match_declarations(&vc, "probe_dyn_dispatch_prune");
    });
}

#[test]
fn test_prune_worklist_bound_covers_observed_loop_array_propagation() {
    with_test_ay_ctx_for_source(LOOP_SLICE_PRUNE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_loop_slice_prune");
        let body = instance.body().expect("body");
        let fn_name = "probe_loop_slice_prune";
        let mem_cfg =
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() };
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, fn_name, mem_cfg);

        chc_ctx.declare_block_relations();
        chc_ctx.declare_error_relation();
        chc_ctx.emit_entry_rule();
        chc_ctx.generate_transition_rules();

        let (iterations, max_iters, block_count, array_count, max_preds) =
            observed_nonlocal_worklist_iterations(&chc_ctx);
        assert!(block_count > 1, "{fn_name}: expected multi-block CFG");
        assert!(array_count > 0, "{fn_name}: expected at least one live heap array");
        assert!(max_preds > 0, "{fn_name}: expected backward propagation predecessors");
        assert!(
            iterations <= max_iters,
            "{fn_name}: observed propagation iterations ({iterations}) should stay within bound \
             ({max_iters})"
        );

        chc_ctx.prune_vc_unused_type_arrays();
        assert_relation_apps_match_declarations(&chc_ctx.vc, fn_name);
    });
}
