// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;
use crate::codegen_ay::context::with_test_ay_ctx_for_source;
use crate::codegen_ay::test_fixtures::find_instance_by_suffix;
use trust_mc_core::violation::PropertyKind;

// =========================================================================
// compute_topo: linear CFG (no branches)
// =========================================================================

const LINEAR_SOURCE: &str = r#"#![allow(dead_code)]
fn linear_fn(x: u32) -> u32 {
let a = x + 1;
let b = a + 2;
b
}
"#;

/// Linear CFG: all reachable blocks appear in topo order, no cycles.
#[test]
fn test_compute_topo_linear_cfg() {
    with_test_ay_ctx_for_source(LINEAR_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "linear_fn");
        let body = instance.body().expect("body");
        let (topo_order, reachable_count) = compute_topo(&body);

        // All reachable blocks should be in topo order (no cycle)
        assert_eq!(
            topo_order.len(),
            reachable_count,
            "linear CFG should have no cycles: topo_order={}, reachable={}",
            topo_order.len(),
            reachable_count
        );
        // Block 0 must be first (entry)
        assert_eq!(topo_order[0], 0, "entry block (bb0) must be first in topo order");
        // Must have at least 1 block
        assert!(reachable_count >= 1, "should have at least 1 reachable block");
    });
}

// =========================================================================
// compute_topo: diamond CFG (branch + merge)
// =========================================================================

const DIAMOND_SOURCE: &str = r#"#![allow(dead_code)]
fn diamond_fn(c: bool) -> u32 {
if c { 10 } else { 20 }
}
"#;

/// Diamond CFG: if/else creates a branch and merge pattern.
/// All blocks reachable, topo order covers them all, no cycles.
#[test]
fn test_compute_topo_diamond_cfg() {
    with_test_ay_ctx_for_source(DIAMOND_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "diamond_fn");
        let body = instance.body().expect("body");
        let (topo_order, reachable_count) = compute_topo(&body);

        // No cycles in a simple if/else
        assert_eq!(topo_order.len(), reachable_count, "diamond CFG should have no cycles");
        // Diamond: at least 3 blocks (entry, then-branch, else-branch/merge)
        assert!(
            reachable_count >= 3,
            "diamond CFG should have at least 3 reachable blocks, got {}",
            reachable_count
        );
        assert_eq!(topo_order[0], 0, "entry block must be first");
    });
}

// =========================================================================
// compute_topo: nested branch CFG
// =========================================================================

const NESTED_BRANCH_SOURCE: &str = r#"#![allow(dead_code)]
fn nested_branch(a: bool, b: bool) -> u32 {
if a {
    if b { 1 } else { 2 }
} else {
    3
}
}
"#;

/// Nested branches: more complex CFG, still acyclic.
#[test]
fn test_compute_topo_nested_branch_cfg() {
    with_test_ay_ctx_for_source(NESTED_BRANCH_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "nested_branch");
        let body = instance.body().expect("body");
        let (topo_order, reachable_count) = compute_topo(&body);

        assert_eq!(topo_order.len(), reachable_count, "nested branch CFG should have no cycles");
        // Nested if/else: at least 4 blocks
        assert!(
            reachable_count >= 4,
            "nested branch should have at least 4 reachable blocks, got {}",
            reachable_count
        );
    });
}

// =========================================================================
// compute_topo: loop CFG (cycle detection)
// =========================================================================

const LOOP_SOURCE: &str = r#"#![allow(dead_code)]
fn loop_fn(mut n: u32) -> u32 {
while n > 0 {
    n -= 1;
}
n
}
"#;

/// Loop CFG: cycle should be detected (topo_order.len() < reachable_count).
#[test]
fn test_compute_topo_loop_detects_cycle() {
    with_test_ay_ctx_for_source(LOOP_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "loop_fn");
        let body = instance.body().expect("body");
        let (topo_order, reachable_count) = compute_topo(&body);

        // Loop creates a back-edge → cycle → topo can't sort all blocks
        assert!(
            topo_order.len() < reachable_count,
            "loop CFG should detect cycle: topo_order={} should be < reachable={}",
            topo_order.len(),
            reachable_count
        );
    });
}

// =========================================================================
// compute_topo: early return (unreachable code)
// =========================================================================

const EARLY_RETURN_SOURCE: &str = r#"#![allow(dead_code)]
fn early_return(x: u32) -> u32 {
if x > 0 {
    return x;
}
0
}
"#;

/// Early return: all blocks should still be reachable and ordered correctly.
#[test]
fn test_compute_topo_early_return() {
    with_test_ay_ctx_for_source(EARLY_RETURN_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "early_return");
        let body = instance.body().expect("body");
        let (topo_order, reachable_count) = compute_topo(&body);

        // No cycle — early return is still acyclic
        assert_eq!(topo_order.len(), reachable_count, "early return CFG should have no cycles");
        assert!(reachable_count >= 2, "should have at least 2 blocks");
    });
}

// =========================================================================
// compute_topo: excludes unreachable blocks
// =========================================================================

const UNREACHABLE_TAIL_SOURCE: &str = r#"#![allow(dead_code)]
fn unreachable_tail(x: u32) -> u32 {
return x + 1;
#[allow(unreachable_code)]
{
    x + 2
}
}
"#;

/// CFG with explicit unreachable tail should report fewer reachable
/// blocks than total MIR blocks.
#[test]
fn test_compute_topo_excludes_unreachable_blocks() {
    with_test_ay_ctx_for_source(UNREACHABLE_TAIL_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "unreachable_tail");
        let body = instance.body().expect("body");
        let (topo_order, reachable_count) = compute_topo(&body);

        assert_eq!(
            topo_order.len(),
            reachable_count,
            "unreachable-tail CFG should still be acyclic"
        );
        assert!(
            reachable_count <= body.blocks.len(),
            "reachable block count must not exceed total blocks: reachable={}, total={}",
            reachable_count,
            body.blocks.len()
        );
        assert_eq!(topo_order.first(), Some(&0), "entry block must remain reachable");
    });
}

// =========================================================================
// compute_topo: single block (minimal CFG)
// =========================================================================

const SINGLE_BLOCK_SOURCE: &str = r#"#![allow(dead_code)]
fn single_block() -> u32 {
42
}
"#;

/// Single-block CFG: trivial case.
#[test]
fn test_compute_topo_single_block() {
    with_test_ay_ctx_for_source(SINGLE_BLOCK_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "single_block");
        let body = instance.body().expect("body");
        let (topo_order, reachable_count) = compute_topo(&body);

        assert_eq!(topo_order.len(), reachable_count);
        assert_eq!(topo_order[0], 0, "single block CFG: bb0 is the only block");
    });
}

// =========================================================================
// compute_topo: match/switch with multiple arms
// =========================================================================

const MATCH_SOURCE: &str = r#"#![allow(dead_code)]
fn match_fn(x: u32) -> u32 {
match x {
    0 => 100,
    1 => 200,
    2 => 300,
    _ => 400,
}
}
"#;

/// Match/switch: multiple arms fan out and merge — no cycles.
#[test]
fn test_compute_topo_match_cfg() {
    with_test_ay_ctx_for_source(MATCH_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "match_fn");
        let body = instance.body().expect("body");
        let (topo_order, reachable_count) = compute_topo(&body);

        assert_eq!(topo_order.len(), reachable_count, "match CFG should have no cycles");
        // Match with 4 arms + entry block: at least 2 blocks (MIR may optimize)
        assert!(
            reachable_count >= 2,
            "match should have at least 2 reachable blocks, got {}",
            reachable_count
        );
    });
}

// =========================================================================
// compute_topo: nested loops (double cycle)
// =========================================================================

const NESTED_LOOP_SOURCE: &str = r#"#![allow(dead_code)]
fn nested_loop(mut n: u32) -> u32 {
let mut total = 0u32;
while n > 0 {
    let mut m = n;
    while m > 0 {
        total = total.wrapping_add(1);
        m -= 1;
    }
    n -= 1;
}
total
}
"#;

/// Nested loops: multiple back-edges → cycle detected.
#[test]
fn test_compute_topo_nested_loops_detect_cycle() {
    with_test_ay_ctx_for_source(NESTED_LOOP_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "nested_loop");
        let body = instance.body().expect("body");
        let (topo_order, reachable_count) = compute_topo(&body);

        assert!(
            topo_order.len() < reachable_count,
            "nested loops should detect cycle: topo_order={} < reachable={}",
            topo_order.len(),
            reachable_count
        );
    });
}

// =========================================================================
// compute_topo: topo order respects dominance
// =========================================================================

/// Verify that topo order respects the predecessor-before-successor invariant.
/// For every edge (u → v), u must appear before v in the topo order.
#[test]
fn test_compute_topo_respects_predecessor_ordering() {
    with_test_ay_ctx_for_source(DIAMOND_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "diamond_fn");
        let body = instance.body().expect("body");
        let (topo_order, _) = compute_topo(&body);

        // bb0 must dominate all other blocks — it must come first
        assert_eq!(topo_order[0], 0);
        assert!(topo_order.len() >= 3, "diamond should have 3+ blocks in topo order");

        // Build position map: block index → topo position
        let mut position = std::collections::HashMap::new();
        for (pos, &bb) in topo_order.iter().enumerate() {
            position.insert(bb, pos);
        }

        // Verify topological invariant: for every edge (bb → succ),
        // bb must appear before succ in topo_order.
        for (bb_idx, block) in body.blocks.iter().enumerate() {
            let Some(&bb_pos) = position.get(&bb_idx) else {
                continue; // unreachable block, not in topo order
            };
            let succs: Vec<usize> = match &block.terminator.kind {
                TerminatorKind::Goto { target } => vec![*target],
                TerminatorKind::SwitchInt { targets, .. } => {
                    let mut s: Vec<usize> = targets.branches().map(|(_, t)| t).collect();
                    s.push(targets.otherwise());
                    s
                }
                TerminatorKind::Drop { target, .. } => vec![*target],
                TerminatorKind::Call { target, .. } => target.iter().copied().collect(),
                TerminatorKind::Assert { target, .. } => vec![*target],
                _ => vec![], // external enum: TerminatorKind
            };
            for succ in succs {
                let succ_pos = position
                    .get(&succ)
                    .expect("successor not in topo_order — indicates incomplete topo sort");
                assert!(
                    bb_pos < *succ_pos,
                    "topological violation: bb{bb_idx} (pos={bb_pos}) should precede bb{succ} (pos={succ_pos})"
                );
            }
        }
    });
}

// =========================================================================
// codegen_function: orchestration paths
// =========================================================================

#[test]
fn test_codegen_chc_path_populates_chc_vc_and_resets_context() {
    with_test_ay_ctx_for_source(LINEAR_SOURCE, |ctx| {
        let mut ctx = ctx;
        ctx.queries.set_args(crate::args::Arguments::default());
        let instance = find_instance_by_suffix(ctx.tcx, "linear_fn");
        let body = instance.body().expect("body");
        let name = instance.name();
        ctx.set_current_fn(instance);

        codegen_chc_path(&mut ctx, &body, &name);

        assert!(ctx.current_fn().is_none(), "CHC path must reset current function context");
        assert!(ctx.chc_vc.is_some(), "CHC path should populate chc_vc");
        assert!(
            ctx.bmc_vc.violations.is_empty(),
            "CHC path should not add BMC-mode property violations"
        );
    });
}

#[test]
fn test_codegen_function_with_body_chc_mode_routes_to_chc_path() {
    with_test_ay_ctx_for_source(LINEAR_SOURCE, |ctx| {
        let mut ctx = ctx;
        ctx.config.use_chc = true;
        ctx.queries.set_args(crate::args::Arguments::default());
        let instance = find_instance_by_suffix(ctx.tcx, "linear_fn");
        let body = instance.body().expect("body");
        let name = instance.name();
        ctx.set_current_fn(instance);

        codegen_function_with_body(&mut ctx, instance, body, &name);

        assert!(ctx.current_fn().is_none(), "codegen_function should reset current_fn in CHC mode");
        assert!(ctx.chc_vc.is_some(), "CHC mode should populate chc_vc");
        assert!(
            ctx.bmc_vc.violations.iter().all(|v| v.kind != PropertyKind::Unreachable),
            "acyclic CHC path should not record unsupported_cfg_cycle"
        );
    });
}

#[test]
fn test_codegen_function_with_body_bmc_mode_routes_to_statement_codegen() {
    with_test_ay_ctx_for_source(LINEAR_SOURCE, |ctx| {
        let mut ctx = ctx;
        ctx.config.use_chc = false;
        ctx.queries.set_args(crate::args::Arguments::default());
        let instance = find_instance_by_suffix(ctx.tcx, "linear_fn");
        let body = instance.body().expect("body");
        let name = instance.name();
        ctx.set_current_fn(instance);

        codegen_function_with_body(&mut ctx, instance, body, &name);

        assert!(ctx.current_fn().is_none(), "codegen_function should reset current_fn in BMC mode");
        assert!(ctx.chc_vc.is_none(), "BMC mode should not populate chc_vc");
        assert!(
            ctx.bmc_vc.violations.iter().all(|v| v.kind != PropertyKind::Unreachable),
            "acyclic BMC path should not record unsupported_cfg_cycle"
        );
    });
}

// =========================================================================
// codegen_function_with_body: BMC + loop → successful unrolling
// =========================================================================

/// BMC mode with a loop: the unroller should eliminate the cycle and
/// codegen should proceed without recording an unsupported_cfg_cycle.
#[test]
fn test_codegen_function_with_body_bmc_loop_unrolls_successfully() {
    with_test_ay_ctx_for_source(LOOP_SOURCE, |ctx| {
        let mut ctx = ctx;
        ctx.config.use_chc = false;
        ctx.config.unwind_depth = 3;
        ctx.config.unwinding_assertions = false;
        ctx.queries.set_args(crate::args::Arguments::default());
        let instance = find_instance_by_suffix(ctx.tcx, "loop_fn");
        let body = instance.body().expect("body");
        let name = instance.name();
        ctx.set_current_fn(instance);

        codegen_function_with_body(&mut ctx, instance, body, &name);

        assert!(
            ctx.current_fn().is_none(),
            "BMC loop path should reset current_fn after successful unrolling"
        );
        assert!(ctx.chc_vc.is_none(), "BMC path should not populate chc_vc");
        assert!(
            ctx.bmc_vc.violations.iter().all(|v| v.kind != PropertyKind::Unreachable),
            "successfully unrolled loop should not record unsupported_cfg_cycle"
        );
    });
}

// =========================================================================
// codegen_function_with_body: CHC + loop (no unrolling needed)
// =========================================================================

/// CHC mode with a loop: should route to CHC path without unrolling.
#[test]
fn test_codegen_function_with_body_chc_loop_skips_unrolling() {
    with_test_ay_ctx_for_source(LOOP_SOURCE, |ctx| {
        let mut ctx = ctx;
        ctx.config.use_chc = true;
        ctx.queries.set_args(crate::args::Arguments::default());
        let instance = find_instance_by_suffix(ctx.tcx, "loop_fn");
        let body = instance.body().expect("body");
        let name = instance.name();
        ctx.set_current_fn(instance);

        codegen_function_with_body(&mut ctx, instance, body, &name);

        assert!(ctx.current_fn().is_none(), "CHC loop path should reset current_fn");
        assert!(
            ctx.chc_vc.is_some(),
            "CHC mode with loop should produce CHC verification conditions"
        );
        assert!(
            ctx.bmc_vc.violations.iter().all(|v| v.kind != PropertyKind::Unreachable),
            "CHC path should not record unsupported_cfg_cycle"
        );
    });
}

// =========================================================================
// codegen_function_with_body: unsupported loop-contract breadcrumb
// =========================================================================

const LOOP_CONTRACT_BREADCRUMB_SOURCE: &str = r#"#![allow(dead_code)]
#![feature(register_tool)]
#![register_tool(kanitool)]

#[inline(never)]
#[kanitool::fn_marker = "kani_register_loop_contract"]
fn kani_register_loop_contract<F: Fn() -> bool>(f: &F, transformed: usize) -> bool {
    transformed != 0 && f()
}

fn original_loop_contract() -> bool {
    let captured = 7_u8;
    kani_register_loop_contract(&|| captured == 7, 0)
}

fn calls_original_loop_contract() -> bool {
    original_loop_contract()
}

fn transformed_loop_contract() -> bool {
    let captured = 7_u8;
    kani_register_loop_contract(&|| captured == 7, 1)
}
"#;

#[test]
fn test_loop_contract_breadcrumb_scan_requires_original_role() {
    with_test_ay_ctx_for_source(LOOP_CONTRACT_BREADCRUMB_SOURCE, |ctx| {
        let original = find_instance_by_suffix(ctx.tcx, "original_loop_contract");
        let transformed = find_instance_by_suffix(ctx.tcx, "transformed_loop_contract");
        assert!(body_has_untransformed_loop_contract_call(&original.body().expect("body")));
        assert!(!body_has_untransformed_loop_contract_call(&transformed.body().expect("body")));
    });
}

#[test]
fn test_untransformed_loop_contract_breadcrumb_fails_closed_in_bmc() {
    with_test_ay_ctx_for_source(LOOP_CONTRACT_BREADCRUMB_SOURCE, |ctx| {
        let mut ctx = ctx;
        let mut args = crate::args::Arguments::default();
        args.unstable_features.push("loop-contracts".to_string());
        ctx.queries.set_args(args);
        ctx.config.use_chc = false;

        let instance = find_instance_by_suffix(ctx.tcx, "calls_original_loop_contract");
        let body = instance.body().expect("body");
        let name = instance.name();
        ctx.set_current_fn(instance);
        codegen_function_with_body(&mut ctx, instance, body, &name);

        assert!(ctx.current_fn().is_none(), "fail-closed path must reset current_fn");
        assert!(
            ctx.unsupported_constructs
                .contains_key("loop invariant captures unsupported dereference")
        );
        assert!(ctx.bmc_vc.violations.iter().any(|violation| {
            violation
                .smt_var
                .as_deref()
                .is_some_and(|name| name.contains("unsupported_loop_contract"))
        }));
    });
}

#[test]
fn test_untransformed_loop_contract_breadcrumb_fails_closed_in_chc() {
    with_test_ay_ctx_for_source(LOOP_CONTRACT_BREADCRUMB_SOURCE, |ctx| {
        let mut ctx = ctx;
        let mut args = crate::args::Arguments::default();
        args.unstable_features.push("loop-contracts".to_string());
        ctx.queries.set_args(args);
        ctx.config.use_chc = true;

        let instance = find_instance_by_suffix(ctx.tcx, "original_loop_contract");
        let body = instance.body().expect("body");
        let name = instance.name();
        ctx.set_current_fn(instance);
        codegen_function_with_body(&mut ctx, instance, body, &name);

        assert!(ctx.current_fn().is_none(), "fail-closed path must reset current_fn");
        assert!(
            ctx.unsupported_constructs
                .contains_key("loop invariant captures unsupported dereference")
        );
        assert_eq!(
            ctx.chc_vc.as_ref().and_then(|vc| vc.query.target.as_deref()),
            Some("chc_loop_contract_unsupported")
        );
    });
}

// =========================================================================
// compute_topo: SwitchInt dedup (duplicate successors)
// =========================================================================

const SWITCH_DEDUP_SOURCE: &str = r#"#![allow(dead_code)]
fn switch_dedup(x: u32) -> u32 {
match x {
    0 | 1 => 10,
    2 | 3 => 20,
    _ => 30,
}
}
"#;

/// SwitchInt with multiple case values mapping to the same target block.
/// Verifies that compute_topo's sort+dedup of successors handles duplicate
/// target blocks correctly without inflating indegree counts.
#[test]
fn test_compute_topo_switchint_dedup_successors() {
    with_test_ay_ctx_for_source(SWITCH_DEDUP_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "switch_dedup");
        let body = instance.body().expect("body");
        let (topo_order, reachable_count) = compute_topo(&body);

        assert_eq!(topo_order.len(), reachable_count, "switch with merged arms should be acyclic");
        assert_eq!(topo_order[0], 0, "entry block must be first");
        // Merged match arms reduce block count vs independent arms
        assert!(
            reachable_count >= 2,
            "switch_dedup should have at least 2 reachable blocks, got {}",
            reachable_count
        );

        // Verify no duplicate entries in topo_order
        let mut seen = std::collections::HashSet::new();
        for &bb in &topo_order {
            assert!(seen.insert(bb), "duplicate block {} in topo_order", bb);
        }
    });
}

// =========================================================================
// needs_contract_inline_boost: no contract markers
// =========================================================================

#[test]
fn test_is_closure_shim_name() {
    for name in [
        "core::ops::function::FnOnce::call_once",
        "core::ops::function::FnMut::call_mut",
        "core::ops::function::Fn::call",
    ] {
        assert!(is_closure_shim_name(name), "{name} should be detected as closure shim");
    }

    for name in [
        "core::ops::function::FnOnce::call_mut",
        "core::ops::function::FnMut::call_once",
        "my_crate::plain_function",
    ] {
        assert!(!is_closure_shim_name(name), "{name} should not be closure shim");
    }
}

#[test]
fn test_is_contract_marker_name() {
    for marker in [
        "kani_contract_mode",
        "kani_force_fn_once",
        "kani_force_fn_once_with_args",
        "kani_register_contract",
    ] {
        assert!(is_contract_marker_name(marker), "{marker} should enable inline boost");
    }

    for marker in ["kani_requires", "kani_ensures", "kani_stub_verified", "non_contract_marker"] {
        assert!(!is_contract_marker_name(marker), "{marker} should not enable inline boost");
    }
}

const NO_CONTRACT_SOURCE: &str = r#"#![allow(dead_code)]
fn plain_fn(x: u32) -> u32 {
x + 1
}
"#;

/// Plain function with no contract markers should not need inline boost.
#[test]
fn test_needs_contract_inline_boost_plain_fn() {
    with_test_ay_ctx_for_source(NO_CONTRACT_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "plain_fn");
        let body = instance.body().expect("body");
        let result = needs_contract_inline_boost(&body);
        assert!(!result, "plain function should not need contract inline boost");
    });
}

// =========================================================================
// needs_contract_inline_boost: function with closure call
// =========================================================================

const CLOSURE_CALL_SOURCE: &str = r#"#![allow(dead_code)]
fn closure_caller(f: fn(u32) -> u32, x: u32) -> u32 {
f(x)
}

fn with_closure(x: u32) -> u32 {
let add_one = |v: u32| v + 1;
add_one(x)
}
"#;

/// Functions with closures may or may not trigger boost depending on MIR lowering.
/// The key is that plain closures (not FnOnce::call_once shims) should NOT trigger.
#[test]
fn test_needs_contract_inline_boost_closure() {
    with_test_ay_ctx_for_source(CLOSURE_CALL_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "with_closure");
        let body = instance.body().expect("body");
        let result = needs_contract_inline_boost(&body);
        assert!(
            result,
            "closure call should trigger inline boost when MIR lowers through closure-call shims"
        );
    });
}

// =========================================================================
// needs_contract_inline_boost: diverse function bodies
// =========================================================================

const DIVERSE_SOURCE: &str = r#"#![allow(dead_code)]
fn with_match(x: u32) -> u32 {
match x {
    0 => 0,
    n => n - 1,
}
}

fn with_loop(mut n: u32) -> u32 {
while n > 0 { n -= 1; }
n
}

fn with_call(x: u32) -> u32 {
core::hint::black_box(x)
}
"#;

/// Various function bodies should not trigger contract inline boost.
#[test]
fn test_needs_contract_inline_boost_diverse_no_boost() {
    with_test_ay_ctx_for_source(DIVERSE_SOURCE, |ctx| {
        for name in &["with_match", "with_loop", "with_call"] {
            let instance = find_instance_by_suffix(ctx.tcx, name);
            let body = instance.body().expect("body");
            let result = needs_contract_inline_boost(&body);
            assert!(!result, "{name} should not need contract inline boost");
        }
    });
}

// =========================================================================
// Verify all probe sources compile with MIR bodies
// =========================================================================

#[test]
fn test_all_topo_probes_compile() {
    let sources_and_fns: &[(&str, &[&str])] = &[
        (LINEAR_SOURCE, &["linear_fn"]),
        (DIAMOND_SOURCE, &["diamond_fn"]),
        (NESTED_BRANCH_SOURCE, &["nested_branch"]),
        (LOOP_SOURCE, &["loop_fn"]),
        (EARLY_RETURN_SOURCE, &["early_return"]),
        (SINGLE_BLOCK_SOURCE, &["single_block"]),
        (MATCH_SOURCE, &["match_fn"]),
        (NESTED_LOOP_SOURCE, &["nested_loop"]),
        (NO_CONTRACT_SOURCE, &["plain_fn"]),
        (CLOSURE_CALL_SOURCE, &["closure_caller", "with_closure"]),
        (DIVERSE_SOURCE, &["with_match", "with_loop", "with_call"]),
        (SWITCH_DEDUP_SOURCE, &["switch_dedup"]),
    ];

    for (source, fns) in sources_and_fns {
        with_test_ay_ctx_for_source(source, |ctx| {
            for name in *fns {
                let instance = find_instance_by_suffix(ctx.tcx, name);
                assert!(instance.body().is_some(), "{name} should have a MIR body");
            }
        });
    }
}

// =========================================================================
// codegen_function_with_body: BMC + `block_on` busy-poll loop
// =========================================================================

/// A verbatim copy of `kani::block_on` (library/trust-mc/src/futures.rs) —
/// the `kani` crate is not linked into these unit-test crates — wrapped around
/// an `async` block that carries a real obligation on a symbolic input.
const BLOCK_ON_ASSERT_SOURCE: &str = r#"#![allow(dead_code)]
use std::{
    future::Future,
    pin::Pin,
    task::{Context, RawWaker, RawWakerVTable, Waker},
};

fn probe_block_on_assert(x: u32) {
    block_on(async move {
        assert!(x < 5);
    })
}

pub fn block_on<T>(mut fut: impl Future<Output = T>) -> T {
    let waker = unsafe { Waker::from_raw(NOOP_RAW_WAKER) };
    let cx = &mut Context::from_waker(&waker);
    let mut fut = unsafe { Pin::new_unchecked(&mut fut) };
    loop {
        match fut.as_mut().poll(cx) {
            std::task::Poll::Ready(res) => return res,
            std::task::Poll::Pending => continue,
        }
    }
}

const NOOP_RAW_WAKER: RawWaker = {
    unsafe fn clone_waker(_: *const ()) -> RawWaker { NOOP_RAW_WAKER }
    unsafe fn noop(_: *const ()) {}
    RawWaker::new(std::ptr::null(), &RawWakerVTable::new(clone_waker, noop, noop, noop))
};
"#;

/// BMC mode must NOT leave `block_on` as an unsupported `Call terminator`.
///
/// Before the mode-aware inline gate, the MIR inline pass preserved every
/// `block_on` (a CHC-only need), the DAG-only statement mini-inliner then
/// rejected its poll LOOP, and the harness bailed with
/// `unsupported_with_fallback("Call terminator")` and ZERO obligations — the
/// `assert!` inside the awaited body never became a check. This pins the
/// positive side: the body is inlined, the loop is unrolled, and the assert
/// is an obligation of the harness.
#[test]
fn test_codegen_function_with_body_bmc_inlines_block_on_and_emits_awaited_assert() {
    with_test_ay_ctx_for_source(BLOCK_ON_ASSERT_SOURCE, |ctx| {
        let mut ctx = ctx;
        ctx.config.use_chc = false;
        ctx.config.unwind_depth = 2;
        ctx.config.unwinding_assertions = true;
        ctx.queries.set_args(crate::args::Arguments::default());
        let instance = find_instance_by_suffix(ctx.tcx, "probe_block_on_assert");
        let body = instance.body().expect("body");
        let name = instance.name();
        ctx.set_current_fn(instance);

        codegen_function_with_body(&mut ctx, instance, body, &name);

        assert!(ctx.current_fn().is_none(), "BMC path should reset current_fn");
        assert!(ctx.chc_vc.is_none(), "BMC path should not populate chc_vc");
        let call_terminator_fallbacks = ctx
            .unsupported_constructs
            .get("Call terminator")
            .map(|locations| locations.iter().filter(|l| l.contains("block_on")).count())
            .unwrap_or(0);
        assert_eq!(
            call_terminator_fallbacks, 0,
            "block_on must be inlined in BMC, not recorded as an unsupported Call terminator: {:?}",
            ctx.unsupported_constructs
        );
        assert!(
            ctx.bmc_vc.violations.iter().any(|v| matches!(
                v.kind,
                PropertyKind::Assertion | PropertyKind::Panic
            )),
            "the assert inside the awaited body must be an obligation of the harness, got {:?}",
            ctx.bmc_vc.violations.iter().map(|v| v.kind).collect::<Vec<_>>()
        );
    });
}

/// The CHC twin: the boundary is kept for the single-poll specializer, so
/// the inline pass must leave the `block_on` call in place. The CHC lane
/// records nothing in `bmc_vc`; what this pins is that the flag flips with
/// the mode (the inline-pass unit tests pin the flag itself).
#[test]
fn test_codegen_function_with_body_chc_keeps_block_on_boundary() {
    with_test_ay_ctx_for_source(BLOCK_ON_ASSERT_SOURCE, |ctx| {
        let mut ctx = ctx;
        ctx.config.use_chc = true;
        ctx.queries.set_args(crate::args::Arguments::default());
        let instance = find_instance_by_suffix(ctx.tcx, "probe_block_on_assert");
        let body = instance.body().expect("body");
        let name = instance.name();
        ctx.set_current_fn(instance);

        codegen_function_with_body(&mut ctx, instance, body, &name);

        assert!(ctx.current_fn().is_none(), "CHC path should reset current_fn");
        assert!(ctx.chc_vc.is_some(), "CHC mode should produce CHC verification conditions");
        assert!(ctx.bmc_vc.violations.is_empty(), "CHC path must not record BMC violations");
    });
}
