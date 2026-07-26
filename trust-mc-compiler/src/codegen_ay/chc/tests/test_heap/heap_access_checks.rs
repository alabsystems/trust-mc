// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;

// =====================================================================
// Part of #1178: Tests for heap_access_checks integration
// =====================================================================
//
// heap_access_checks() generates safety checks for memory load/store:
// 1. obj_valid[obj_id] == true (use-after-free check)
// 2. offset % align == 0 (alignment check, if align > 1)
// 3. offset + access_size <= obj_size[obj_id] (bounds check)
// 4. offset + access_size >= offset (no-wrap check)
//
// These checks are collected in pending_checks, drained during
// encode_block_statements, and converted to error rules via
// emit_error_rule_for_condition.

#[test]
fn test_heap_access_validity_check_pattern() {
    // (#1178) Verify validity check pattern: obj_valid.select(obj_id)
    // This detects use-after-free: accessing memory after deallocation.

    let obj_valid = Expr::var("obj_valid", Sort::array(Sort::bitvec(32), Sort::bool()));
    let obj_id = Expr::bitvec_const(1, 32);

    // Pattern: select(obj_valid, obj_id) must be true
    let validity_check = obj_valid.select(obj_id);

    assert!(validity_check.sort().is_bool(), "Validity check must be Bool");

    let smt = validity_check.to_string();
    assert!(smt.contains("select"), "Should use select: {}", smt);
    assert!(smt.contains("obj_valid"), "Should reference obj_valid: {}", smt);
}

#[test]
fn test_heap_access_stack_local_validity_is_literal_true() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_stack_local_access(x: u32) -> u32 { x }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_stack_local_access");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            "probe_stack_local_access",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );

        let addr = chc_ctx.get_or_create_local_address(1).expect("local address");
        let checks = chc_ctx.heap_access_checks(addr, body.locals()[1].ty);

        assert!(
            checks.first().is_some_and(|check| matches!(check.value(), ExprValue::BoolConst(true))),
            "stack-local validity should be a literal true check, got: {checks:?}"
        );
    });
}

#[test]
fn test_known_stack_address_provenance_records_stack_only() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_stack_local_access(x: u32) -> u32 { x }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_stack_local_access");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            "probe_stack_local_access",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );

        let addr = chc_ctx.get_or_create_local_address(1).expect("local address");
        assert!(chc_ctx.record_known_stack_addr_expr(1, addr.clone(), "test"));
        assert_eq!(
            ChcCtx::try_extract_constant_addr(
                &chc_ctx.known_stack_addr_expr(1).expect("recorded stack address")
            ),
            ChcCtx::try_extract_constant_addr(&addr)
        );

        let folded_addr = addr.clone().extract(63, 0);
        assert!(
            chc_ctx.record_known_stack_addr_expr(2, folded_addr, "test-folded"),
            "stack address wrapped in constant BV syntax should still be recorded"
        );
        assert_eq!(
            ChcCtx::try_extract_constant_addr(
                &chc_ctx.known_stack_addr_expr(2).expect("recorded folded stack address")
            ),
            ChcCtx::try_extract_constant_addr(&addr)
        );

        let heap_like_addr = Expr::bitvec_const(0x777_u32, 32).concat(Expr::bitvec_const(0, 32));
        assert!(!chc_ctx.record_known_stack_addr_expr(3, heap_like_addr, "test"));
        assert!(chc_ctx.known_stack_addr_expr(3).is_none());
    });
}

#[test]
fn test_heap_access_alignment_check_pattern() {
    // (#1178) Verify alignment check pattern: offset % align == 0
    // This detects misaligned access (UB in Rust).

    let offset = Expr::var("offset", Sort::bitvec(32));
    let align = Expr::bitvec_const(8, 32); // 8-byte alignment
    let zero = Expr::bitvec_const(0, 32);

    // Pattern: (offset bvurem align) == 0
    let rem = offset.bvurem(align);
    let alignment_check = rem.eq(zero);

    assert!(alignment_check.sort().is_bool(), "Alignment check must be Bool");

    let smt = alignment_check.to_string();
    assert!(smt.contains("bvurem"), "Should use bvurem for remainder: {}", smt);
}

#[test]
fn test_heap_access_bounds_check_pattern() {
    // (#1178) Verify bounds check pattern: offset + size <= obj_size[obj_id]
    // This detects buffer overflow/underflow.

    let obj_size = Expr::var("obj_size", Sort::array(Sort::bitvec(32), Sort::bitvec(32)));
    let obj_id = Expr::var("obj_id", Sort::bitvec(32));
    let offset = Expr::var("offset", Sort::bitvec(32));
    let access_size = Expr::bitvec_const(8, 32); // 8-byte access

    // Pattern: offset + access_size <= obj_size[obj_id]
    let end_offset = offset.bvadd(access_size);
    let alloc_size = obj_size.select(obj_id);
    let bounds_check = end_offset.bvule(alloc_size);

    assert!(bounds_check.sort().is_bool(), "Bounds check must be Bool");

    let smt = bounds_check.to_string();
    assert!(smt.contains("bvadd"), "Should compute end offset: {}", smt);
    assert!(smt.contains("bvule"), "Should use unsigned <= for bounds: {}", smt);
    assert!(smt.contains("select"), "Should select from obj_size: {}", smt);
}

#[test]
fn test_heap_access_no_wrap_check_pattern() {
    // (#1178) Verify no-wrap check pattern: offset + size >= offset
    // This detects arithmetic overflow in offset calculation.

    let offset = Expr::var("offset", Sort::bitvec(32));
    let access_size = Expr::bitvec_const(8, 32);

    // Pattern: (offset + size) >= offset (no wrap-around)
    let end_offset = offset.clone().bvadd(access_size);
    let no_wrap_check = end_offset.bvuge(offset);

    assert!(no_wrap_check.sort().is_bool(), "No-wrap check must be Bool");

    let smt = no_wrap_check.to_string();
    assert!(smt.contains("bvuge"), "Should use unsigned >= for wrap check: {}", smt);
}

#[test]
fn test_heap_access_checks_combined_conjunction() {
    // (#1178) Verify all checks can be combined: validity ∧ align ∧ bounds ∧ no_wrap
    // In actual codegen, each check generates a separate error rule, but
    // they could also be combined if needed.

    let obj_valid = Expr::var("obj_valid", Sort::array(Sort::bitvec(32), Sort::bool()));
    let obj_size = Expr::var("obj_size", Sort::array(Sort::bitvec(32), Sort::bitvec(32)));
    let obj_id = Expr::bitvec_const(1, 32);
    let offset = Expr::var("offset", Sort::bitvec(32));
    let access_size = Expr::bitvec_const(4, 32);
    let align = Expr::bitvec_const(4, 32);
    let zero = Expr::bitvec_const(0, 32);

    // Build all checks
    let valid = obj_valid.select(obj_id.clone());
    let aligned = offset.clone().bvurem(align).eq(zero);
    let end = offset.clone().bvadd(access_size);
    let bounds = end.clone().bvule(obj_size.select(obj_id));
    let no_wrap = end.bvuge(offset);

    // Combine: valid ∧ aligned ∧ bounds ∧ no_wrap
    let all_checks = valid.and(aligned).and(bounds).and(no_wrap);

    assert!(all_checks.sort().is_bool(), "Combined checks must be Bool");
}

#[test]
fn test_obj_valid_check_detects_use_after_free() {
    // (#1176) Verify obj_valid check detects use-after-free.
    // After deallocation, obj_valid[obj_id] = false, so accessing memory
    // at that obj_id triggers a validity check failure.
    //
    // Flow:
    // 1. RustDealloc sets: obj_valid__out = store(obj_valid, obj_id, false)
    // 2. On deref, heap_access_checks generates: select(obj_valid, obj_id)
    // 3. emit_error_rule_for_condition creates: from ∧ !check → error
    //
    // When obj_valid[obj_id] = false:
    // - The check expression evaluates to false
    // - Negated: !false = true, making the error rule body satisfiable
    // - AY finds a counterexample, detecting the UAF

    let obj_valid = Expr::var("obj_valid", Sort::array(Sort::bitvec(32), Sort::bool()));
    let obj_id = Expr::bitvec_const(1, 32);

    // Simulate dealloc: store false at obj_id
    let after_dealloc = obj_valid.store(obj_id.clone(), Expr::bool_const(false));

    // Check validity after dealloc (what heap_access_checks generates)
    let validity_check = after_dealloc.select(obj_id);

    // This check is now: select(store(obj_valid, 1, false), 1) = false
    // When this reaches emit_error_rule_for_condition:
    // - condition = false
    // - violation = !condition = true
    // - error rule becomes: from_rel ∧ constraints ∧ true → error
    // - This is satisfiable, so AY reports an error (UAF detected)

    assert!(validity_check.sort().is_bool(), "Validity check must be Bool");

    let smt = validity_check.to_string();
    assert!(smt.contains("select"), "Should use select: {}", smt);
    assert!(smt.contains("store"), "Should reflect the dealloc store: {}", smt);
    assert!(smt.contains("false"), "Should contain false from dealloc: {}", smt);
}

#[test]
fn test_error_rule_pattern_for_safety_violation() {
    // (#1176) Verify error rule pattern: from ∧ constraints ∧ !check → error
    // When a safety check fails (e.g., obj_valid = false for UAF),
    // emit_error_rule_for_condition creates this rule pattern.

    // Simulate a failed validity check (UAF scenario)
    let validity_check = Expr::bool_const(false); // Object was freed

    // emit_error_rule_for_condition does: violation = !check
    let violation = validity_check.not();

    // The error rule body is: from_rel ∧ stmt_constraints ∧ violation
    // When validity_check = false, violation = true
    // This makes the rule body satisfiable, triggering an error

    // Verify the negation produces true
    assert!(violation.sort().is_bool(), "Violation must be Bool");

    // For a constant false input, .not() gives true
    let smt = violation.to_string();
    assert!(
        smt.contains("not") || smt.contains("true"),
        "Negating false validity should produce error: {}",
        smt
    );
}

// =====================================================================
// heap_span_access_checks: copy/copy_nonoverlapping/write_bytes spans
// =====================================================================

#[test]
fn test_heap_span_access_checks_symbolic_count_emits_bounds() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_span_checks(x: [u8; 4]) -> [u8; 4] { x }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_span_checks");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            "probe_span_checks",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );

        let addr = chc_ctx.get_or_create_local_address(1).expect("local address");
        let elem_ty = rustc_public::ty::Ty::unsigned_ty(rustc_public::ty::UintTy::U8);
        let count = Expr::var("n", Sort::bitvec(64));

        let checks = chc_ctx.heap_span_access_checks(&addr, elem_ty, &count);

        // u8 span over a known stack local: span-fits-u32, no-wrap, bounds.
        // (No alignment check for align-1 elements.)
        assert_eq!(checks.len(), 3, "expected span-fits/no-wrap/bounds, got: {checks:?}");
        let all = checks.iter().map(ToString::to_string).collect::<Vec<_>>().join("\n");
        assert!(all.contains("bvuge"), "no-wrap check must be present: {all}");
        assert!(all.contains("bvule"), "allocation bounds check must be present: {all}");
    });
}

#[test]
fn test_heap_span_access_checks_skips_symbolic_provenance() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_span_skip(x: [u8; 4]) -> [u8; 4] { x }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_span_skip");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            "probe_span_skip",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );

        // A raw symbolic pointer has unknown provenance: the allocation size
        // is a caller contract we cannot invent, so no checks are emitted
        // (historical skip; precision plan Step 5 owns this residual).
        let addr = Expr::var("p", Sort::bitvec(64));
        let elem_ty = rustc_public::ty::Ty::unsigned_ty(rustc_public::ty::UintTy::U8);
        let count = Expr::var("n", Sort::bitvec(64));

        let checks = chc_ctx.heap_span_access_checks(&addr, elem_ty, &count);
        assert!(checks.is_empty(), "symbolic obj_id must keep the skip, got: {checks:?}");
    });
}
